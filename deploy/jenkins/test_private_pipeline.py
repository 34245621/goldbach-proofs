import base64
import hashlib
import hmac
import importlib.util
import io
import json
import sqlite3
import tempfile
import time
import unittest
from pathlib import Path
from threading import BoundedSemaphore
from unittest.mock import MagicMock, patch

import event_jobs
import jenkins_dispatch
import merge_proofs
from formal_proof import judge
from prepare_proof import ProofRefused
from verify_proof import ProofRejected

_WEBHOOK_SPEC = importlib.util.spec_from_file_location(
    "receive_webhook_mod",
    Path(__file__).resolve().with_name("receive-webhook.py"),
)
receive_webhook = importlib.util.module_from_spec(_WEBHOOK_SPEC)
_WEBHOOK_SPEC.loader.exec_module(receive_webhook)

SECRET = b"desk-secret-32-bytes-minimum-key!!"


def make_upload_ticket(secret, payload):
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    enc = base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")
    sig = hmac.new(secret, enc.encode("ascii"), hashlib.sha256).hexdigest()
    return f"{enc}.{sig}"


class PrivateSubmissionPipelineTests(unittest.TestCase):
    def test_streaming_bundle_pack_and_unpack_validates_hashes_and_magic(self):
        lean_bytes = b"import Mathlib\ntheorem Conjectures.Goldbach.Demo : True := trivial\n"
        kproof_bytes = b"KPRF\x01\x00\x01\x02\x03" * 2048
        now = int(time.time())
        ticket_data = {
            "v": 1,
            "problem": "goldbach",
            "gap": "L-goldbach-demo",
            "kind": "prove",
            "module": "Conjectures.Goldbach.Demo",
            "file": "lean/Conjectures/Goldbach/Demo.lean",
            "statement": "True",
            "statement_sha256": hashlib.sha256(b"True").hexdigest(),
            "imports": [],
            "handle": "alice",
            "github_uid": 12345,
            "submission_id": "a" * 40,
            "source_sha256": hashlib.sha256(lean_bytes).hexdigest(),
            "kproof_sha256": hashlib.sha256(kproof_bytes).hexdigest(),
            "throttled": False,
            "expires_at": now + 600,
        }
        signed = make_upload_ticket(SECRET, ticket_data)
        verified = receive_webhook.verify_upload_ticket(SECRET, signed, now)
        self.assertEqual(verified["submission_id"], "a" * 40)

        from deploy.desk import sign_upload_ticket, verify_upload_ticket
        long_ticket = dict(ticket_data, statement="∀ n : ℕ, " * 900 + "True")
        legacy = make_upload_ticket(SECRET, long_ticket)
        self.assertGreater(len(legacy), 4096)
        compact = sign_upload_ticket(SECRET, long_ticket)
        self.assertLess(len(compact), 4096)
        for verify in (verify_upload_ticket, receive_webhook.verify_upload_ticket):
            for ticket in (legacy, compact):
                self.assertEqual(verify(SECRET, ticket, now), long_ticket)
                self.assertIsNone(verify(SECRET, ticket, now + 601))
                self.assertIsNone(verify(b"wrong-key", ticket, now))

        compressed = receive_webhook.pack_submission_bundle(lean_bytes, kproof_bytes)
        with tempfile.TemporaryDirectory() as folder:
            dest = Path(folder)
            receive_webhook.stream_unpack_bundle(
                io.BytesIO(compressed), len(compressed), verified, dest,
            )
            self.assertEqual((dest / "proof.lean").read_bytes(), lean_bytes)
            self.assertEqual((dest / "proof.kproof").read_bytes(), kproof_bytes)

            # Also verify HTTP/1.1 Transfer-Encoding: chunked streaming (used by nginx HTTP/2 -> HTTP/1.1 unbuffered proxy)
            chunked_wire = bytearray()
            for idx in range(0, len(compressed), 37):
                piece = compressed[idx:idx + 37]
                chunked_wire.extend(f"{len(piece):x}\r\n".encode("ascii"))
                chunked_wire.extend(piece)
                chunked_wire.extend(b"\r\n")
            chunked_wire.extend(b"0\r\n\r\n")
            dest_chunked = dest / "chunked"
            dest_chunked.mkdir()
            reader = receive_webhook._ChunkedBodyReader(io.BytesIO(bytes(chunked_wire)), max_bytes=len(compressed) + 16)
            receive_webhook.stream_unpack_bundle(reader, None, verified, dest_chunked)
            self.assertEqual((dest_chunked / "proof.lean").read_bytes(), lean_bytes)
            self.assertEqual((dest_chunked / "proof.kproof").read_bytes(), kproof_bytes)

            with self.assertRaises(receive_webhook.BundleError) as over_ctx:
                small_reader = receive_webhook._ChunkedBodyReader(io.BytesIO(bytes(chunked_wire)), max_bytes=10)
                receive_webhook.stream_unpack_bundle(small_reader, None, verified, dest_chunked)
            self.assertEqual(over_ctx.exception.status, 413)

            bad_ticket = {**verified, "source_sha256": "0" * 64}
            with self.assertRaises(receive_webhook.BundleError) as ctx:
                receive_webhook.stream_unpack_bundle(
                    io.BytesIO(compressed), len(compressed), bad_ticket, dest,
                )
            self.assertEqual(ctx.exception.status, 422)

            bad_kp = b"XXXX\x0112345"
            bad_compressed = receive_webhook.pack_submission_bundle(lean_bytes, bad_kp)
            bad_kp_ticket = {**verified, "kproof_sha256": hashlib.sha256(bad_kp).hexdigest()}
            with self.assertRaises(receive_webhook.BundleError) as ctx2:
                receive_webhook.stream_unpack_bundle(
                    io.BytesIO(bad_compressed), len(bad_compressed), bad_kp_ticket, dest,
                )
            self.assertEqual(ctx2.exception.code, "invalid_kproof_magic")

    def test_fast_track_priority_and_adaptive_slow_cap_in_jenkins_dispatch(self):
        # Verify dynamic slow-pool headroom schedule across fast_inflight = 0..12
        expected_caps = {0: 8, 1: 7, 2: 6, 3: 5, 4: 4, 5: 3, 6: 2, 7: 2, 8: 2, 9: 2, 10: 2, 11: 1, 12: 0}
        for fast_n, cap in expected_caps.items():
            self.assertEqual(jenkins_dispatch.slow_authoritative_cap(fast_n), cap)

        # Case 1: 2 fast + 2 private_slow + 6 legacy_pr -> 2 fast, 2 private_slow, 4 legacy_pr (6 slow total, 4 free headroom)
        db = sqlite3.connect(":memory:")
        event_jobs.initialize(db)
        jenkins_dispatch.initialize(db)
        with db:
            for idx in range(1, 7):
                db.execute(
                    "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, ?, ?, ?)",
                    (idx, f"{idx:040x}", 4000 + idx, str(9000 + idx), f"pr:{idx}"),
                )
            for idx in (7, 8):
                sub = f"{idx:040x}"
                db.execute(
                    "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, 0, ?, ?)",
                    (idx, sub, f"bundle:slow:{sub}", f"upload:{idx}"),
                )
            for idx in (9, 10):
                sub = f"{idx:040x}"
                db.execute(
                    "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, 0, ?, ?)",
                    (idx, sub, f"bundle:fast:{sub}", f"upload:{idx}"),
                )

        enqueued_order = []
        client = MagicMock()
        client.enqueue.side_effect = lambda name, params: (enqueued_order.append(params["CI_JOB_ID"]) or (100 + params["CI_JOB_ID"]))

        jenkins_dispatch.dispatch(db, client, {
            "authoritative": "goldbach-formal-isolated",
            "authoritative-pr": "goldbach-formal-isolated",
        })
        self.assertEqual(enqueued_order, [9, 10, 7, 8, 1, 2, 3, 4])

        # Case 2: Under heavy Fast-Track load (6 fast inflight), slow pool automatically shrinks back to 2-slot floor
        db2 = sqlite3.connect(":memory:")
        event_jobs.initialize(db2)
        jenkins_dispatch.initialize(db2)
        with db2:
            for idx in range(1, 7):
                sub = f"{idx:040x}"
                db2.execute(
                    "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, 0, ?, ?)",
                    (idx, sub, f"bundle:fast:{sub}", f"upload:{idx}"),
                )
                db2.execute(
                    "INSERT INTO jenkins_dispatches VALUES (?, 'goldbach-formal-isolated', ?, ?, NULL)",
                    (idx, 200 + idx, 300 + idx),
                )
            for idx in range(11, 15):
                db2.execute(
                    "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, ?, ?, ?)",
                    (idx, f"{idx:040x}", 5000 + idx, str(9000 + idx), f"pr:{idx}"),
                )
        enqueued_heavy = []
        client2 = MagicMock()
        client2.enqueue.side_effect = lambda name, params: (enqueued_heavy.append(params["CI_JOB_ID"]) or (500 + params["CI_JOB_ID"]))
        jenkins_dispatch.dispatch(db2, client2, {
            "authoritative": "goldbach-formal-isolated",
            "authoritative-pr": "goldbach-formal-isolated",
        })
        self.assertEqual(enqueued_heavy, [11, 12])

    def test_two_stage_formal_judge_kproof_short_circuit_and_moderation(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            submissions = root / "submissions"
            db = sqlite3.connect(":memory:")
            event_jobs.initialize(db)

            def setup_bundle(job_id, sub_id, *, with_kproof=True):
                bdir = submissions / sub_id
                bdir.mkdir(parents=True, exist_ok=True)
                lean_src = b"import Mathlib\ntheorem Conjectures.Goldbach.Demo : True := trivial\n"
                (bdir / "proof.lean").write_bytes(lean_src)
                kp_sha = None
                if with_kproof:
                    kp = b"KPRF\x01demo"
                    (bdir / "proof.kproof").write_bytes(kp)
                    kp_sha = hashlib.sha256(kp).hexdigest()
                ticket = {
                    "v": 1,
                    "problem": "goldbach",
                    "gap": "L-goldbach-demo",
                    "kind": "prove",
                    "module": "Conjectures.Goldbach.Demo",
                    "file": "lean/Conjectures/Goldbach/Demo.lean",
                    "statement": "True",
                    "statement_sha256": hashlib.sha256(b"True").hexdigest(),
                    "imports": [],
                    "handle": "alice",
                    "github_uid": 555,
                    "submission_id": sub_id,
                    "source_sha256": hashlib.sha256(lean_src).hexdigest(),
                    "kproof_sha256": kp_sha,
                    "throttled": False,
                    "expires_at": int(time.time()) + 600,
                }
                (bdir / "ticket.json").write_text(json.dumps(ticket), encoding="utf-8")
                with db:
                    db.execute(
                        "INSERT INTO ci_jobs VALUES (?, 'authoritative', ?, 0, ?, ?)",
                        (job_id, sub_id, f"bundle:fast:{sub_id}", f"upload:{sub_id}"),
                    )
                return bdir

            def fake_prepare(bundle_dir, base, work):
                (work / "gap.id").write_text("L-goldbach-demo\n")
                (work / "statement.txt").write_text("True")
                (work / "task.kind").write_text("prove")
                (work / "pr.module").write_text("Conjectures.Goldbach.Demo\n")
                (work / "proof.lean").write_bytes((bundle_dir / "proof.lean").read_bytes())
                if (bundle_dir / "proof.kproof").is_file():
                    (work / "proof.kproof").write_bytes((bundle_dir / "proof.kproof").read_bytes())
                return "lean/Conjectures/Goldbach/Demo.lean"

            # Case 1: Stage-1 KProof tamper (sorryAx) -> instant permanent ban, 0 Stage-2 verify() calls!
            sub1 = "1" * 40
            setup_bundle(1, sub1)
            kp_worker = MagicMock()
            kp_worker.verify_kproof.side_effect = ProofRejected("REJECTED (sorry): theorem uses sorryAx")
            work1 = root / "w1"
            work1.mkdir()
            with patch("formal_proof.precheck"), \
                 patch("formal_proof.prepare_bundle", side_effect=fake_prepare), \
                 patch("formal_proof.authorize"), \
                 patch("formal_proof.report_moderation") as rep_mod, \
                 patch("formal_proof.verify") as stage2_verify:
                run1 = judge(
                    db, None, 1, work1, root, root, root,
                    desk_url="https://desk.example", secret=SECRET,
                    submissions_dir=submissions, kproof_worker=kp_worker,
                    slow_slots=BoundedSemaphore(2),
                )
            stage2_verify.assert_not_called()
            rep_mod.assert_called_once()
            self.assertEqual(rep_mod.call_args.kwargs["kind"], "tamper")
            payload1 = json.loads(db.execute("SELECT payload FROM desk_outbox WHERE run=?", (run1,)).fetchone()[0])
            self.assertEqual(payload1["verdict"], "REJECTED")

            # Case 2: Stage-1 KProof passes -> Stage-2 hits 124 timeout -> stage2_resource_limit strike!
            sub2 = "2" * 40
            bdir2 = setup_bundle(2, sub2)
            kp_worker2 = MagicMock()
            kp_worker2.verify_kproof.return_value = {"rests_on": [], "defs": []}
            work2 = root / "w2"
            work2.mkdir()
            with patch("formal_proof.precheck"), \
                 patch("formal_proof.prepare_bundle", side_effect=fake_prepare), \
                 patch("formal_proof.authorize"), \
                 patch("formal_proof.report_kernel_verified", return_value={"throttled": False}) as rep_kv, \
                 patch("formal_proof.report_moderation", return_value={"strikes": 1, "action": "warn"}) as rep_mod2, \
                 patch("formal_proof.report_diagnostic"), \
                 patch("formal_proof.verify", side_effect=ProofRejected("REJECTED (timeout): Lean compilation exceeded the 20-minute time limit")):
                judge(
                    db, None, 2, work2, root, root, root,
                    desk_url="https://desk.example", secret=SECRET,
                    submissions_dir=submissions, kproof_worker=kp_worker2,
                    slow_slots=BoundedSemaphore(2),
                )
            rep_kv.assert_called_once()
            rep_mod2.assert_called_once()
            self.assertEqual(rep_mod2.call_args.kwargs["kind"], "stage2_resource_limit")
            self.assertFalse(bdir2.exists())

            # Case 3: Stage-1 passes + Stage-2 ACCEPTED -> kproof deleted, proof.lean preserved for merge_proofs!
            sub3 = "3" * 40
            bdir3 = setup_bundle(3, sub3)
            work3 = root / "w3"
            work3.mkdir()
            accepted_manifest = {
                "rests_on": [{"module": "Conjectures.Goldbach.Demo", "sha256": "f" * 64}],
                "defs": [],
            }
            with patch("formal_proof.precheck"), \
                 patch("formal_proof.prepare_bundle", side_effect=fake_prepare), \
                 patch("formal_proof.authorize"), \
                 patch("formal_proof.report_kernel_verified", return_value={"throttled": False}), \
                 patch("formal_proof.report_diagnostic"), \
                 patch("formal_proof.verify", return_value=accepted_manifest):
                judge(
                    db, None, 3, work3, root, root, root,
                    desk_url="https://desk.example", secret=SECRET,
                    submissions_dir=submissions, kproof_worker=kp_worker2,
                    slow_slots=BoundedSemaphore(2),
                )
            self.assertFalse((bdir3 / "proof.kproof").exists())
            self.assertTrue((bdir3 / "proof.lean").is_file())

            # Case 4: Throttled actor uses dedicated throttled_slots instead of borrowed slow_slots!
            sub4 = "4" * 40
            bdir4 = setup_bundle(4, sub4)
            work4 = root / "w4"
            work4.mkdir()
            entered = []

            class TrackedSlot:
                def __init__(self, label):
                    self.label = label
                def __enter__(self):
                    entered.append(self.label)
                def __exit__(self, *exc):
                    return False

            with patch("formal_proof.precheck"), \
                 patch("formal_proof.prepare_bundle", side_effect=fake_prepare), \
                 patch("formal_proof.authorize"), \
                 patch("formal_proof.report_kernel_verified", return_value={"throttled": True}), \
                 patch("formal_proof.report_diagnostic"), \
                 patch("formal_proof.verify", return_value=accepted_manifest):
                judge(
                    db, None, 4, work4, root, root, root,
                    desk_url="https://desk.example", secret=SECRET,
                    submissions_dir=submissions, kproof_worker=kp_worker2,
                    slow_slots=TrackedSlot("slow"),
                    throttled_slots=TrackedSlot("throttled"),
                )
            self.assertEqual(entered, ["throttled"])

    def test_merge_private_commits_directly_to_main_reports_published_and_cleans_bundle(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            store = root / "store"
            base = store / "init-base"
            (base / "lean").mkdir(parents=True)
            (base / "research").mkdir(parents=True)
            store.mkdir(exist_ok=True)
            (store / "current").symlink_to(base)

            trust_blobs = {}
            for name in merge_proofs.TRUST_FILES:
                data = f"pinned-{name}\n".encode()
                (base / "lean" / name).write_bytes(data)
                trust_blobs[f"lean/{name}"] = merge_proofs.git_blob(data)

            (base / "research/gaps.json").write_text(json.dumps({"gaps": [{
                "id": "L-goldbach-demo",
                "module": "Conjectures.Goldbach.Demo",
                "file": "lean/Conjectures/Goldbach/Demo.lean",
                "statement": "True",
            }]}))
            (base / "research/problems.json").write_text("{}")

            sub_id = "d" * 40
            submissions = root / "submissions"
            bdir = submissions / sub_id
            bdir.mkdir(parents=True)
            proof_content = b"import Mathlib\ntheorem Conjectures.Goldbach.Demo : True := trivial\n"
            proof_sha256 = hashlib.sha256(proof_content).hexdigest()
            proof_git_blob = merge_proofs.git_blob(proof_content)
            (bdir / "proof.lean").write_bytes(proof_content)
            (bdir / "ticket.json").write_text(json.dumps({
                "handle": "alice", "github_uid": 88888, "submission_id": sub_id,
            }))

            db = sqlite3.connect(":memory:")
            event_jobs.initialize(db)
            jenkins_dispatch.initialize(db)
            db.execute("CREATE TABLE desk_outbox (run INTEGER, attempt INTEGER, payload TEXT, delivered INTEGER)")
            record = {
                "lemma_id": "L-goldbach-demo",
                "kind": "prove",
                "module": "Conjectures.Goldbach.Demo",
                "head_sha": sub_id,
                "verdict": "ACCEPTED",
                "run_id": 9001,
                "run_attempt": 1,
                "manifest": {
                    "rests_on": [{"module": "Conjectures.Goldbach.Demo", "sha256": proof_sha256}],
                    "defs": [],
                },
            }
            with db:
                db.execute("INSERT INTO ci_jobs VALUES (10, 'authoritative', ?, 0, ?, 'upload')", (sub_id, f"bundle:fast:{sub_id}"))
                db.execute("INSERT INTO desk_runs VALUES (10, 9001)")
                db.execute("INSERT INTO desk_outbox VALUES (9001, 1, ?, 1)", (json.dumps(record),))
                db.execute("INSERT INTO jenkins_dispatches VALUES (10, 'goldbach-formal-isolated', 1, 1, 'SUCCESS')")

            main_sha = "e" * 40
            base_tree_sha = "b" * 40
            new_tree_sha = "c" * 40
            committed_sha = "f" * 40
            commits_created = []

            def fake_api(method, path, body=None):
                if method == "GET" and path.endswith("/git/ref/heads/main"):
                    return {"object": {"sha": main_sha}}
                if method == "GET" and path.endswith(f"/git/commits/{main_sha}"):
                    return {"sha": main_sha, "tree": {"sha": base_tree_sha}}
                if method == "GET" and path.endswith(f"/git/trees/{base_tree_sha}?recursive=1"):
                    return {
                        "sha": base_tree_sha,
                        "truncated": False,
                        "tree": [
                            {"path": p, "type": "blob", "mode": "100644", "sha": s}
                            for p, s in trust_blobs.items()
                        ],
                    }
                if method == "POST" and path.endswith("/git/blobs"):
                    return {"sha": proof_git_blob}
                if method == "POST" and path.endswith("/git/trees"):
                    return {"sha": new_tree_sha}
                if method == "POST" and path.endswith("/git/commits"):
                    commits_created.append(body)
                    return {"sha": committed_sha}
                if method == "PATCH" and path.endswith("/git/refs/heads/main"):
                    self.assertEqual(body, {"sha": committed_sha, "force": False})
                    return {"object": {"sha": committed_sha}}
                if method == "GET" and f"/contents/lean/Conjectures/Goldbach/Demo.lean?ref={committed_sha}" in path:
                    return {"type": "file", "path": "lean/Conjectures/Goldbach/Demo.lean", "sha": proof_git_blob}
                if method == "GET" and "/check-runs?" in path:
                    return {"check_runs": []}
                if method == "POST" and path.endswith("/check-runs"):
                    return {"id": 777001}
                raise AssertionError(f"Unexpected GitHub API call: {method} {path}")

            app = MagicMock()
            app.request.side_effect = fake_api
            with patch("merge_proofs.report_published") as rep_pub:
                merge_proofs.drain(
                    db, app, store, 1,
                    submissions_dir=submissions,
                    desk_url="https://desk.example",
                    desk_secret=SECRET,
                )

            self.assertEqual(len(commits_created), 1)
            self.assertEqual(
                commits_created[0]["author"],
                {"name": "alice", "email": "88888+alice@users.noreply.github.com"},
            )
            rep_pub.assert_called_once_with(
                "https://desk.example",
                SECRET,
                run_id=9001,
                gap="L-goldbach-demo",
                commit_sha=committed_sha,
                check_id=777001,
            )
            self.assertFalse(bdir.exists())  # private bundle cleaned up after main commit!
            published_base = (store / "current").resolve()
            self.assertEqual(
                (published_base / "lean/Conjectures/Goldbach/Demo.lean").read_bytes(),
                proof_content,
            )

    def test_prepare_dep_kproofs_handles_cross_device_stage_dir(self):
        import errno
        import os
        import stat
        import verify_proof

        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            work = root / "work"
            project = root / "project"
            toolchain = root / "toolchain"
            req_dir = root / "stage" / "req-1"
            work.mkdir()
            req_dir.mkdir(parents=True)
            mod = "Conjectures.Cuts.Task000000000000000000000001"
            src = project / "Conjectures/Cuts/Task000000000000000000000001.lean"
            src.parent.mkdir(parents=True)
            src.write_bytes(b"import Mathlib\ntheorem t : True := trivial\n")
            worker = verify_proof.KProofWorker(root / "stage")

            def fake_run(cmd, **kwargs):
                out_dir = work / "kproof-deps-out"
                if "-o" in cmd:
                    art = Path(cmd[cmd.index("-o") + 1]).name
                    (out_dir / art).write_bytes(b"OLEAN")
                elif "--export-kproof" in cmd:
                    kp = Path(cmd[cmd.index("--export-kproof") + 2]).name
                    (out_dir / kp).write_bytes(b"KPRF\x01dep")
                return MagicMock(returncode=0)

            real_rename = os.rename

            def cross_device_rename(src_path, dst_path):
                if str(dst_path).endswith("dep_0.kproof"):
                    raise OSError(errno.EXDEV, "Invalid cross-device link", str(src_path), str(dst_path))
                return real_rename(src_path, dst_path)

            with patch.dict(os.environ, {}, clear=False), \
                 patch.object(verify_proof.os, "chown"), \
                 patch.object(verify_proof.subprocess, "check_output", return_value=str(project)), \
                 patch.object(verify_proof.subprocess, "run", side_effect=fake_run), \
                 patch("shutil.os.rename", side_effect=cross_device_rename):
                os.environ.pop("GOLDBACH_LEAN_DEP_CACHE", None)
                staged = worker._prepare_dep_kproofs([mod], work, project, toolchain, root / "own.sh", req_dir)

            self.assertEqual(staged, ["/stage/req-1/dep_0.kproof"])
            kp_file = req_dir / "dep_0.kproof"
            self.assertEqual(kp_file.read_bytes(), b"KPRF\x01dep")
            self.assertEqual(stat.S_IMODE(kp_file.stat().st_mode), 0o644)
            self.assertFalse((work / "kproof-deps-out" / "dep_0.kproof").exists())


if __name__ == "__main__":
    unittest.main()
