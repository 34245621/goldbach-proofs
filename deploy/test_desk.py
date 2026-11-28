import hashlib
import hmac
import io
import json
import os
import secrets
import sqlite3
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing, redirect_stdout
from pathlib import Path
from unittest.mock import patch

from deploy import github_identity
from deploy.desk import Desk, NO_RESEARCH_DEADLINE, RECOVER_FAILURE_IP_LIMIT, _RECOVER_FAILURES, fleet_pass
from tools import goldbach as cli

GAPS = [
    {"id": f"L-goldbach-{i:03}", "statement": f"True {-i}"}
    for i in range(1, 6)
]
SECRET = b"test-secret"
BASE = "/api/desk/"
START = 1_000_000


class DeskTests(unittest.TestCase):
    def setUp(self):
        _RECOVER_FAILURES.clear()
        folder = self.enterContext(tempfile.TemporaryDirectory())
        self.enterContext(patch.dict(os.environ, {"XDG_STATE_HOME": folder}))
        self.db = Path(folder) / "verdicts.sqlite3"
        self.desk = Desk(self.db, GAPS, SECRET)

    def test_parallel_shortlists_distribute_and_count_other_attempts(self):
        ids = [gap["id"] for gap in GAPS]
        self.desk.gaps = {g["id"]: {**g, "parallel": True} for g in GAPS}

        def claim_one(i):
            return self.request("claim", {"handle": f"agent-{i}", "candidates": ids},
                                ip=f"10.{i}.1.1")

        with ThreadPoolExecutor(max_workers=12) as workers:
            receipts = list(workers.map(claim_one, range(100)))
        self.assertTrue(all(code == 201 for code, _ in receipts), [r for r in receipts if r[0] != 201])
        for gap in ids:
            loads = sorted(r["active_claims"] for _, r in receipts if r["gap"]["id"] == gap)
            self.assertEqual(loads, list(range(20)))
        first = receipts[0][1]
        self.assertEqual(self.submit(first["lease"]["token"])[0], 200)
        with self.desk.transaction() as conn:
            self.assertEqual(self.desk.claim_counts(conn, START)[first["gap"]["id"]], (19, 1))

    def test_challenges_require_explicit_claim(self):
        self.desk.gaps = {g["id"]: {**g, "challenge_only": True} for g in GAPS}
        automatic = {"handle": "alice"}
        self.assertEqual(self.request("claim", automatic)[0], 409)
        self.desk.gaps[GAPS[2]["id"]]["challenge_only"] = False
        code, result = self.request("claim", automatic)
        self.assertEqual(code, 201)
        self.assertEqual(result["gap"]["id"], GAPS[2]["id"])
        self.assertEqual(self.request("claim", {"handle": "bob", "gap": GAPS[0]["id"]})[0], 201)

    def test_closing_new_claims_honors_an_existing_lease(self):
        token = self.claim()
        gap = GAPS[0] | {"parallel": True, "challenge_only": True, "claims_closed": True}
        self.desk = Desk(self.db, [gap], SECRET)
        self.assertEqual(self.request("claim", {"handle": "bob", "gap": gap["id"]}),
                         (409, {"error": "claims_closed"}))
        self.assertEqual(self.request("claim", {"handle": "bob"})[0], 409)
        with patch("deploy.desk.time.time", return_value=START):
            self.assertEqual(self.desk.progress_snapshot(), (0, 1, 0, {gap["id"]}))
        self.assertEqual(self.request("beat", {}, token=token)[0], 200)
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.record(102, gap["id"], "ACCEPTED")
        self.assertEqual(self.desk.progress(), (1, 1, 0))

    def request(self, path, body, *, token=None, sign=False, now=START, ip="2001:db8::1"):
        content = json.dumps(body, separators=(",", ":")).encode()
        headers = {}
        if token is not None:
            headers["Authorization"] = "Bearer " + token
        if sign:
            headers["X-Goldbach-Signature"] = "sha256=" + hmac.new(SECRET, content, hashlib.sha256).hexdigest()
        with patch("deploy.desk.time.time", return_value=now):
            return self.desk.dispatch(BASE + path, body, headers, ip, content)

    def claim(self, handle="Alice", **options):
        status, data = self.request("claim", {"handle": handle, "gap": GAPS[0]["id"]}, **options)
        self.assertEqual(status, 201, data)
        return data["lease"]["token"]

    def submit(self, token, *, pr=8, head="a" * 40):
        return self.request("submit", {"pr": pr, "head": head, "agent": {"model": "test-model", "harness": "codex"}}, token=token)

    def authorization(self, **changes):
        result = {
            "pr": 8,
            "head": "a" * 40,
            "handle": "Alice",
            "gap": GAPS[0]["id"],
            "run_id": 102,
            "statement_sha256": hashlib.sha256(GAPS[0]["statement"].encode()).hexdigest(),
        }
        result.update(changes)
        return result

    def record(self, run_id, lemma_id, verdict, attempt=1):
        data = {"run_id": run_id, "lemma_id": lemma_id, "verdict": verdict, "run_attempt": attempt}
        with closing(sqlite3.connect(self.db)) as conn, conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS verdicts (
                    run_id INTEGER, attempt INTEGER, body BLOB, PRIMARY KEY (run_id, attempt)
                )
            """)
            conn.execute("INSERT INTO verdicts VALUES (?, ?, ?)", (run_id, attempt, json.dumps(data).encode()))
            self.desk.record_verdict(data, conn)

    def status(self, now=START):
        with patch("deploy.desk.time.time", return_value=now):
            return self.desk.public_status()

    def test_pending_pr_keeps_authorization_while_next_task_is_claimed(self):
        first = self.claim()
        self.assertEqual(self.submit(first)[0], 200)
        status, second = self.request("claim", {"handle": "Alice"})
        self.assertEqual(status, 201)
        self.assertNotEqual(second["gap"]["id"], GAPS[0]["id"])
        self.assertEqual(self.request("claim", {"handle": "Alice"})[0], 409)
        self.assertEqual(self.submit(second["lease"]["token"], pr=9, head="b"*40)[0], 200)
        self.assertEqual(self.request("claim", {"handle": "Alice"})[0], 409)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)

    def test_pending_is_private_and_lists_submitted_unchecked_lease(self):
        self.assertEqual(self.request("pending", {})[0], 401)
        token = self.claim()
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "working"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": []})
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "submitted"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": [
            {"pr": 8, "head": "a" * 40, "handle": "alice", "gap": GAPS[0]["id"]}
        ]})
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "checking"})
        self.assertEqual(self.request("pending", {}, sign=True)[1], {"pending": []})

    def test_prior_proofs_are_ineligible_and_uncredited(self):
        self.record(99, GAPS[0]["id"], "ACCEPTED")
        self.assertEqual(self.request("claim", {"handle": "Bob", "gap": GAPS[0]["id"]})[0], 409)
        self.assertEqual(self.request("claim", {"handle": "Bob"})[1]["gap"]["id"], GAPS[1]["id"])
        self.assertEqual(self.status()["leaderboard"], [])

    def test_participants_can_claim_the_same_gap_concurrently(self):
        def claim(i):
            return self.desk.claim({"handle": f"Agent{i}", "gap": GAPS[0]["id"]}, f"192.0.2.{i}", START)[0]

        with ThreadPoolExecutor(max_workers=8) as workers:
            outcomes = list(workers.map(claim, range(1, 17)))
        self.assertEqual(outcomes, [201] * 16)

    def test_research_claim_survives_a_week_without_heartbeat(self):
        token = self.claim()
        later = START + 7 * 86400
        self.assertEqual(self.status(later)["active"], 1)
        code, lease = self.request("beat", {}, token=token, now=later)
        self.assertEqual(code, 200)
        self.assertEqual(lease["expires_at"], NO_RESEARCH_DEADLINE)
        self.assertEqual(self.request("release", {}, token=token, now=later)[0], 200)
        self.assertEqual(self.status(later)["active"], 0)

    def test_automatic_claim_prefers_a_route_milestone(self):
        self.desk.gaps[GAPS[1]["id"]]["role"] = "endpoint"
        code, result = self.request("claim", {"handle": "alice"})
        self.assertEqual(code, 201)
        self.assertEqual(result["gap"]["id"], GAPS[1]["id"])

    def test_only_a_matching_signed_workflow_can_authorize(self):
        token = self.claim()
        self.assertEqual(self.submit(token)[0], 200)
        self.assertEqual(self.request("authorize", self.authorization())[0], 401)
        for changes in (
            {"head": "b" * 40},
            {"handle": "Mallory"},
            {"statement_sha256": "0" * 64},
            {"pr": 9},
        ):
            self.assertEqual(self.request("authorize", self.authorization(**changes), sign=True)[0], 409)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True), (200, {"authorized": True}))
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.assertEqual(self.request("authorize", self.authorization(run_id=103), sign=True)[0], 409)
        self.assertEqual(self.request("release", {}, token=token)[0], 409)

    def test_unverified_submission_cannot_poison_a_pr_head(self):
        other_status, other = self.request("claim", {"handle": "Mallory", "gap": GAPS[1]["id"]})
        self.assertEqual(other_status, 201)
        self.assertEqual(self.submit(other["lease"]["token"])[0], 200)
        self.assertEqual(self.submit(self.claim())[0], 200)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)

    def test_only_matching_verdict_releases_lease_and_credits_verified_author(self):
        token = self.claim()
        self.assertEqual(self.submit(token)[0], 200)
        before = self.status()
        self.assertFalse(any("handle" in item or "pr" in item for item in before["activities"]))
        self.assertNotIn(token.encode(), self.db.read_bytes())
        self.assertNotIn(b"2001:db8", self.db.read_bytes())
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        self.record(102, GAPS[1]["id"], "ACCEPTED")
        self.assertEqual(self.status()["active"], 1)
        with patch("deploy.desk.time.time", return_value=START + 1):
            self.record(102, GAPS[0]["id"], "ACCEPTED", 2)
        outcome = self.status(START + 1)
        self.assertEqual(outcome["active"], 0)
        self.assertEqual(outcome["activities"][0]["kind"], "accepted")
        self.assertEqual(outcome["leaderboard"], [{"handle": "alice", "accepted": 1}])

    def test_refutation_uses_original_opening_and_shares_first_acceptance(self):
        original, negative = GAPS[:2]
        negative = {**negative, "statement": f'¬ ({original["statement"]})'}
        db = self.db.with_name("refutation.sqlite3")
        desk = Desk(db, [original, negative], SECRET,
                    {original["id"]: START - 360, negative["id"]: START})
        self.assertEqual(desk.points(negative["id"], START), 3)
        with desk.transaction(write=True) as conn:
            for run, gap, handle, points in (
                (1, negative["id"], "refuter", 3), (2, original["id"], "prover", 4)
            ):
                conn.execute("""INSERT INTO goldbach_leases
                    (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at,
                     absolute_expires_at, run_id, finished_at, verdict, points)
                    VALUES (?, ?, '', ?, '', 0, 0, 0, ?, ?, 'ACCEPTED', ?)""",
                    (str(run), gap, handle, run, START + run, points))
        with patch("deploy.desk.time.time", return_value=START + 100):
            rankings = desk.public_status()["rankings"]["all_time"]
        self.assertEqual([(row["handle"], row["points"]) for row in rankings], [("refuter", 3)])

    def test_points_use_publication_age_and_freeze_when_submitted(self):
        gap = GAPS[0]["id"]
        db = self.db.with_name("points.sqlite3")
        self.db = db
        self.desk = Desk(db, GAPS, SECRET, {gap: START - 359})
        self.assertEqual(self.desk.points(gap, START), 2)
        self.assertEqual(self.desk.points(gap, START + 1), 3)
        token = self.claim()
        status, submission = self.submit(token)
        self.assertEqual((status, submission["points"]), (200, 2))
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 200)
        with patch("deploy.desk.time.time", return_value=START + 720):
            self.record(102, gap, "ACCEPTED")
        self.desk = Desk(db, GAPS, SECRET, {gap: START})
        self.assertEqual(self.desk.openings[gap], START - 359)
        self.assertEqual(self.status(START + 720)["rankings"]["all_time"][0]["points"], 2)

    def test_submissions_registered_before_points_keep_their_registration_value(self):
        original, late, retired = GAPS[0]["id"], GAPS[2]["id"], "L-goldbach-retired"
        catalogue = [GAPS[0], {**GAPS[1], "statement": f'¬ ({GAPS[0]["statement"]})'}, *GAPS[2:]]
        db = self.db.with_name("legacy-points.sqlite3")
        Desk(db, catalogue, SECRET, {original: START - 720, late: START + 100})
        with closing(sqlite3.connect(db)) as conn, conn:
            conn.execute("ALTER TABLE goldbach_leases DROP COLUMN points")
            conn.executemany("""INSERT INTO goldbach_leases
                (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at,
                 absolute_expires_at, submitted_at, run_id, finished_at, verdict, model, harness)
                VALUES (?, ?, '', ?, '', 0, 0, 0, ?, ?, ?, 'ACCEPTED', ?, ?)""",
                [("proof", original, "alice", START + 359, 1, START + 400, "model-a", "codex"),
                 ("early", late, "alice", START + 50, 2, START + 401, "model-a", "codex"),
                 ("refutation", catalogue[1]["id"], "bob", START + 360, 3, START + 399, "model-b", "claude-code"),
                 ("retired", retired, "bob", START + 360, 4, START + 403, "model-b", "claude-code")])
            conn.execute("""INSERT INTO goldbach_leases
                (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at, absolute_expires_at)
                VALUES ('claim', ?, '', 'carol', '', 0, 0, 0)""", (late,))
            conn.execute("""INSERT INTO goldbach_leases
                (token_hash, gap, statement_sha256, handle, ip_key, claimed_at, expires_at, absolute_expires_at,
                 submitted_at)
                VALUES ('undated', ?, '', 'carol', '', 0, 0, 0, 'soon')""", (late,))
        reopened = Desk(db, catalogue, SECRET)
        stored = {"proof": 6, "early": 1, "refutation": 7, "retired": 1, "claim": None, "undated": None}
        with reopened.transaction() as conn:
            self.assertEqual(dict(conn.execute("SELECT token_hash, points FROM goldbach_leases")), stored)
        with patch("deploy.desk.time.time", return_value=START + 1000):
            status = reopened.public_status()
        self.assertEqual([(row["handle"], row["accepted"], row["points"]) for row in status["rankings"]["all_time"]],
                         [("bob", 2, 8), ("alice", 1, 1)])
        self.assertEqual(status["agent_rankings"]["models"], [
            {"name": "model-b", "accepted": 2, "points": 8}, {"name": "model-a", "accepted": 1, "points": 1}])
        with Desk(db, catalogue, SECRET, {original: START}).transaction() as conn:
            self.assertEqual(dict(conn.execute("SELECT token_hash, points FROM goldbach_leases")), stored)

    def test_network_limit_groups_ipv6_neighbors_without_leaking_addresses(self):
        for i in range(1, 4):
            self.assertEqual(self.request("claim", {"handle": f"Agent{i}"}, ip=f"2001:db8::{i}")[0], 201)
        self.assertEqual(self.request("claim", {"handle": "Agent4"}, ip="2001:db8::4")[0], 429)
        self.assertEqual(self.request("claim", {"handle": "Agent4"}, ip="2001:db8:0:1::4")[0], 201)

    def test_automatic_claims_spread_across_programs(self):
        programs = ["foundation", "foundation", "coverage", "coverage", "exceptions"]
        self.desk = Desk(self.db, [g | {"program": p} for g, p in zip(GAPS, programs)], SECRET)
        allocated = []
        for handle in ("ada", "bob", "carol"):
            status, assignment = self.request("claim", {"handle": handle})
            self.assertEqual(status, 201)
            allocated.append(assignment["gap"]["program"])
        self.assertEqual(allocated, ["foundation", "coverage", "exceptions"])

    def test_parallel_leases_preserve_checking_and_release_unstarted_after_acceptance(self):
        self.desk = Desk(self.db, [GAPS[0] | {"parallel": False}], SECRET)
        tokens = [self.claim(handle) for handle in ("Alice", "Bob", "Carol")]
        for i, token in enumerate(tokens):
            self.assertEqual(self.submit(token, pr=8+i)[0], 200)
        for i, handle in enumerate(("Alice", "Bob")):
            body = self.authorization(pr=8+i, handle=handle, run_id=102+i)
            self.assertEqual(self.request("authorize", body, sign=True)[0], 200)
        self.assertEqual(self.status()["assignments"], {GAPS[0]["id"]: "checking"})
        with patch("deploy.desk.time.time", return_value=START+1):
            self.record(102, GAPS[0]["id"], "ACCEPTED")
        self.assertEqual(self.request("beat", {}, token=tokens[2])[0], 410)
        self.assertEqual(self.status(START+1)["active"], 1)
        self.assertEqual(self.request("pending", {}, sign=True)[1]["pending"], [])
        self.assertEqual(self.request("claim", {"handle": "Dave", "gap": GAPS[0]["id"]})[0], 409)

    def test_statement_changed_after_claim_cannot_authorize(self):
        self.assertEqual(self.submit(self.claim())[0], 200)
        updated = [GAPS[0] | {"statement": "different statement"}, *GAPS[1:]]
        self.desk = Desk(self.db, updated, SECRET)
        self.assertEqual(self.request("authorize", self.authorization(), sign=True)[0], 409)

    def test_idempotent_claim_replays_lost_response_without_duplicate_lease(self):
        self.assertEqual(self.request("claim", {"handle": "alice", "token": "short"}),
                         (400, {"error": "invalid_claim"}))
        supplied = secrets.token_urlsafe(32)
        code1, first = self.request(
            "claim", {"handle": "Alice", "gap": GAPS[0]["id"], "kind": "cut", "token": supplied}
        )
        self.assertEqual(code1, 201)
        self.assertEqual(first["lease"]["token"], supplied)
        self.assertTrue(first["gap"]["module"].startswith("Conjectures.Cuts.Cut"))

        # Without the client token, the account is blocked by the active unsubmitted lease.
        self.assertEqual(self.request("claim", {"handle": "Alice", "gap": GAPS[0]["id"], "kind": "cut"}),
                         (409, {"error": "handle_already_active"}))

        # Retrying with the same client token replays the exact receipt and module without adding rows.
        code2, replay = self.request(
            "claim", {"handle": "alice", "gap": GAPS[0]["id"], "kind": "cut", "token": supplied}
        )
        self.assertEqual(code2, 201)
        self.assertEqual(replay, first)
        with self.desk.transaction() as conn:
            count, = conn.execute("SELECT COUNT(*) FROM goldbach_leases").fetchone()
        self.assertEqual(count, 1)

        # Mismatched handle, kind, gap, or post-release reuse cannot replay the token.
        for mismatched in (
            {"handle": "bob", "gap": GAPS[0]["id"], "kind": "cut", "token": supplied},
            {"handle": "alice", "gap": GAPS[0]["id"], "kind": "prove", "token": supplied},
            {"handle": "alice", "gap": GAPS[1]["id"], "kind": "cut", "token": supplied},
        ):
            self.assertEqual(self.request("claim", mismatched), (409, {"error": "lease_token_reused"}))
        self.assertEqual(self.request("release", {"reason": "other"}, token=supplied)[0], 200)
        self.assertEqual(
            self.request("claim", {"handle": "alice", "gap": GAPS[0]["id"], "kind": "cut", "token": supplied}),
            (409, {"error": "lease_token_reused"}),
        )

        # If a task's statement changes or it gets solved while the response was lost, replay releases and returns 409.
        token2 = secrets.token_urlsafe(32)
        self.assertEqual(self.request("claim", {"handle": "alice", "gap": GAPS[0]["id"], "token": token2})[0], 201)
        self.desk = Desk(self.db, [GAPS[0] | {"statement": "updated statement"}, *GAPS[1:]], SECRET)
        self.assertEqual(
            self.request("claim", {"handle": "alice", "gap": GAPS[0]["id"], "token": token2}),
            (409, {"error": "no_available_gap"}),
        )
        # Alice is immediately free to claim another task without being stuck in handle_already_active.
        self.assertEqual(self.request("claim", {"handle": "alice", "gap": GAPS[1]["id"]})[0], 201)

    def test_gist_recovery_releases_only_unsubmitted_leases_and_prevents_replay(self):
        # An orphaned unsubmitted lease (lost response / wiped checkout) blocks normal claiming.
        self.claim("skayla2007")
        self.assertEqual(self.request("claim", {"handle": "skayla2007"}),
                         (409, {"error": "handle_already_active"}))

        code, challenge = self.request("recover-challenge", {"handle": "skayla2007"})
        self.assertEqual(code, 200)
        self.assertEqual(len(challenge["leases"]), 1)
        gist_id = "f" * 32
        gist_doc = {
            "id": gist_id,
            "owner": {"id": 4587, "type": "User", "login": "Skayla2007"},
            "files": {github_identity.PROOF_FILENAME: {"truncated": False, "content": challenge["proof_text"]}},
        }

        # Missing challenge, expired window, and cross-purpose Zhihu proof are rejected.
        self.assertEqual(
            self.request(
                "recover",
                {"handle": "skayla2007", "gist": gist_id, "expires_at": challenge["expires_at"]},
            ),
            (400, {"error": "invalid_challenge"}),
        )
        self.assertEqual(
            self.request(
                "recover",
                {
                    "handle": "skayla2007",
                    "challenge": challenge["challenge"],
                    "gist": gist_id,
                    "expires_at": challenge["expires_at"],
                },
                now=challenge["expires_at"],
            ),
            (410, {"error": "challenge_expired"}),
        )
        zhihu_doc = {
            **gist_doc,
            "files": {
                github_identity.PROOF_FILENAME: {
                    "truncated": False,
                    "content": github_identity.proof_text(challenge["challenge"], "skayla2007", purpose="zhihu_link"),
                }
            },
        }
        with patch.object(github_identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(zhihu_doc).encode())
            self.assertEqual(
                self.request(
                    "recover",
                    {
                        "handle": "skayla2007",
                        "challenge": challenge["challenge"],
                        "gist": gist_id,
                        "expires_at": challenge["expires_at"],
                    },
                ),
                (422, {"error": "github_proof_mismatch"}),
            )

        # An attacker IP exhausting its own failed-proof bucket cannot grief skayla2007's IP from recovering.
        for _ in range(RECOVER_FAILURE_IP_LIMIT):
            with patch.object(github_identity.urllib.request, "build_opener") as opener:
                opener.return_value.open.return_value = io.BytesIO(b"{}")
                self.request(
                    "recover",
                    {
                        "handle": "skayla2007",
                        "challenge": challenge["challenge"],
                        "gist": gist_id,
                        "expires_at": challenge["expires_at"],
                    },
                    ip="198.51.100.77",
                )
        self.assertEqual(
            self.request(
                "recover",
                {
                    "handle": "skayla2007",
                    "challenge": challenge["challenge"],
                    "gist": gist_id,
                    "expires_at": challenge["expires_at"],
                },
                ip="198.51.100.77",
            ),
            (429, {"error": "recover_rate_limit"}),
        )

        # End-to-end CLI recover_lease creates a temporary secret gist, releases the orphan, and deletes the gist.
        gh_calls = []
        captured_gist = {}

        def capture_gh(args, **kwargs):
            gh_calls.append(("check_output", tuple(args)))
            if "gists" in args:
                captured_gist["body"] = kwargs["input"].decode("utf-8")
                return json.dumps({"id": gist_id}).encode()
            raise cli.subprocess.CalledProcessError(128, args)

        def fake_run(args, **kwargs):
            gh_calls.append(("run", tuple(args)))
            return None

        def fake_desk(action, data, token=None, *, problem="goldbach"):
            status, body = self.request(action, data, token=token)
            if status >= 400:
                raise cli.DeskRefusal(action, status, body["error"], details=body)
            return body

        with patch.object(cli, "authenticated_login", return_value="skayla2007"), patch.object(
            cli, "desk", side_effect=fake_desk
        ), patch.object(cli.subprocess, "check_output", side_effect=capture_gh), patch.object(
            cli.subprocess, "run", side_effect=fake_run
        ), patch.object(github_identity.urllib.request, "build_opener") as opener, redirect_stdout(io.StringIO()):
            opener.return_value.open.side_effect = lambda req, timeout=6: io.BytesIO(
                json.dumps({
                    **gist_doc,
                    "files": {
                        github_identity.PROOF_FILENAME: {
                            "truncated": False,
                            "content": json.loads(captured_gist["body"])["files"][
                                github_identity.PROOF_FILENAME
                            ]["content"],
                        }
                    },
                }).encode()
            )
            cli.recover_lease("other")

        self.assertIn(("run", ("gh", "api", "--method", "DELETE", f"gists/{gist_id}")), gh_calls)

        # Account can immediately claim a new task; old gist/challenge cannot release the new lease!
        new_token = self.claim("skayla2007")
        with patch.object(github_identity.urllib.request, "build_opener") as opener:
            self.assertEqual(
                self.request(
                    "recover",
                    {
                        "handle": "skayla2007",
                        "challenge": challenge["challenge"],
                        "gist": gist_id,
                        "expires_at": challenge["expires_at"],
                    },
                ),
                (409, {"error": "lease_state_changed"}),
            )
            opener.assert_not_called()

        # Submitted PR leases are never treated as orphaned unsubmitted leases.
        self.assertEqual(self.submit(new_token)[0], 200)
        self.assertEqual(self.request("recover-challenge", {"handle": "skayla2007"}),
                         (404, {"error": "no_unsubmitted_lease"}))

        # Fleet accounts with multiple unsubmitted leases must disambiguate with gap or all=True.
        fpass = fleet_pass(SECRET, "fleet-user", START + 3600)
        with patch("deploy.desk.time.time", return_value=START):
            for idx in (0, 1):
                code, _ = self.desk.dispatch(
                    BASE + "claim", {"handle": "fleet-user", "gap": GAPS[idx]["id"]},
                    {"X-Goldbach-Fleet": fpass}, "198.51.100.9", b"{}",
                )
                self.assertEqual(code, 201)
        self.assertEqual(self.request("recover-challenge", {"handle": "fleet-user"})[0], 409)
        code, scoped = self.request("recover-challenge", {"handle": "fleet-user", "gap": GAPS[0]["id"]})
        self.assertEqual(code, 200)
        scoped_doc = {
            "id": gist_id,
            "owner": {"id": 99, "type": "User", "login": "fleet-user"},
            "files": {github_identity.PROOF_FILENAME: {"truncated": False, "content": scoped["proof_text"]}},
        }
        with patch.object(github_identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(scoped_doc).encode())
            res_code, res_body = self.request(
                "recover",
                {
                    "handle": "fleet-user",
                    "gap": GAPS[0]["id"],
                    "challenge": scoped["challenge"],
                    "gist": gist_id,
                    "expires_at": scoped["expires_at"],
                },
            )
        self.assertEqual((res_code, res_body["gaps"]), (200, [GAPS[0]["id"]]))
        self.assertEqual(len(self.request("recover-challenge", {"handle": "fleet-user"})[1]["leases"]), 1)

        # Valid recoveries do NOT increment failure quota, so shared university NAT users never block one another;
        # only failed Gist proofs (422) count toward RECOVER_FAILURE_IP_LIMIT, and X-Goldbach-Fleet isolates fleets behind NAT.
        nat_ip = "203.0.113.88"
        for _ in range(RECOVER_FAILURE_IP_LIMIT):
            with patch.object(github_identity.urllib.request, "build_opener") as opener:
                opener.return_value.open.return_value = io.BytesIO(b"{}")
                c2 = self.request("recover-challenge", {"handle": "fleet-user"}, ip=nat_ip)[1]
                self.request(
                    "recover",
                    {
                        "handle": "fleet-user",
                        "challenge": c2["challenge"],
                        "gist": gist_id,
                        "expires_at": c2["expires_at"],
                    },
                    ip=nat_ip,
                )
        c3 = self.request("recover-challenge", {"handle": "fleet-user"}, ip=nat_ip)[1]
        self.assertEqual(
            self.request(
                "recover",
                {
                    "handle": "fleet-user",
                    "challenge": c3["challenge"],
                    "gist": gist_id,
                    "expires_at": c3["expires_at"],
                },
                ip=nat_ip,
            ),
            (429, {"error": "recover_rate_limit"}),
        )
        # Even behind that exhausted NAT IP, a registered fleet pass gets its own bucket and succeeds.
        fleet_doc = {
            "id": gist_id,
            "owner": {"id": 99, "type": "User", "login": "fleet-user"},
            "files": {github_identity.PROOF_FILENAME: {"truncated": False, "content": c3["proof_text"]}},
        }
        with patch("deploy.desk.time.time", return_value=START), patch.object(
            github_identity.urllib.request, "build_opener"
        ) as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(fleet_doc).encode())
            code_f, body_f = self.desk.dispatch(
                BASE + "recover",
                {
                    "handle": "fleet-user",
                    "challenge": c3["challenge"],
                    "gist": gist_id,
                    "expires_at": c3["expires_at"],
                },
                {"X-Goldbach-Fleet": fpass},
                nat_ip,
                b"{}",
            )
        self.assertEqual((code_f, body_f["count"]), (200, 1))

    def test_authorize_dry_run_checks_eligibility_without_locking_lease(self):
        token = self.claim(handle="Alice")
        self.assertEqual(self.submit(token)[0], 200)
        dry_body = {
            "pr": 8,
            "head": "a" * 40,
            "handle": "Alice",
            "gap": GAPS[0]["id"],
            "run_id": 102,
            "dry_run": True,
        }
        self.assertEqual(self.request("authorize", dry_body, sign=True), (200, {"authorized": True}))
        # Lease remains unlocked (run_id IS NULL), so release or real authorize with another run_id succeeds.
        self.assertEqual(
            self.request("authorize", self.authorization(run_id=103), sign=True),
            (200, {"authorized": True}),
        )
        # Subsequent dry_run for a different run_id now sees head_already_authorized / submission_unavailable.
        self.assertEqual(self.request("authorize", dry_body | {"run_id": 104}, sign=True)[0], 409)
        self.record(103, GAPS[0]["id"], "ACCEPTED")
        # Another contributor on a parallel or pre-existing lease sees gap_already_proved on dry_run.
        self.assertEqual(
            self.request("authorize", dry_body | {"handle": "Bob", "pr": 9}, sign=True),
            (409, {"error": "no_matching_submission"}),
        )


if __name__ == "__main__":
    unittest.main()
