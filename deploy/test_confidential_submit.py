import contextlib
import hashlib
import io
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from contextlib import closing
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "deploy") not in sys.path:
    sys.path.insert(0, str(ROOT / "deploy"))

from deploy import ban_actor, desk as desk_mod, github_identity
from tools import goldbach as cli


SECRET = b"test-secret-32-bytes-minimum-key!!"
SAMPLE_GAPS = [
    {
        "id": "L-goldbach-priv-1",
        "statement": "∀ n : Nat, n = n",
        "module": "Conjectures.Goldbach.PrivOne",
        "file": "lean/Conjectures/Goldbach/PrivOne.lean",
        "imports": [],
        "plain_statement": {"zh": "测试命题 1", "en": "Test lemma 1"},
    },
    {
        "id": "L-goldbach-priv-2",
        "statement": "∀ m : Nat, m + 0 = m",
        "module": "Conjectures.Goldbach.PrivTwo",
        "file": "lean/Conjectures/Goldbach/PrivTwo.lean",
        "imports": [],
        "plain_statement": {"zh": "测试命题 2", "en": "Test lemma 2"},
    },
]


def sign_body(raw_body):
    import hmac
    return "sha256=" + hmac.new(SECRET, raw_body, hashlib.sha256).hexdigest()


class ConfidentialDeskAndModerationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.state_dir = Path(self.tmp.name)
        self.db_path = self.state_dir / "verdicts.sqlite3"
        self.desk = desk_mod.Desk(
            self.db_path,
            SAMPLE_GAPS,
            SECRET,
            openings={"L-goldbach-priv-1": 1000, "L-goldbach-priv-2": 1000},
            upload_url="https://upload.example/submissions/upload",
        )

    def tearDown(self):
        self.tmp.cleanup()

    def signed_call(self, method_name, payload, now):
        raw = json.dumps(payload).encode("utf-8")
        return getattr(self.desk, method_name)(payload, sign_body(raw), raw, now)

    def issue_pass(self, handle, uid, now=2000):
        status, ch = self.desk.auth_challenge({"handle": handle}, "198.51.100.10", now)
        self.assertEqual(status, 200)
        with patch.object(
            github_identity,
            "verify_gist",
            return_value={"id": uid, "login": handle, "gist_id": "a" * 32},
        ):
            status, verified = self.desk.auth_verify(
                {
                    "handle": handle,
                    "gist": "a" * 32,
                    "challenge": ch["challenge"],
                    "expires_at": ch["expires_at"],
                },
                "198.51.100.10",
                now + 5,
            )
        self.assertEqual(status, 200)
        self.assertEqual(verified["github_uid"], uid)
        return verified["contributor_pass"]

    def test_private_submission_redacts_public_feed_until_accepted_and_published(self):
        now = 2000
        alice_pass = self.issue_pass("alice", 10001, now)
        status, claimed = self.desk.claim(
            {"handle": "alice", "gap": "L-goldbach-priv-1"},
            "198.51.100.10",
            now + 10,
            auth=alice_pass,
        )
        self.assertEqual(status, 201)
        lease_tok = claimed["lease"]["token"]

        src_sha = "1" * 64
        kp_sha = "2" * 64
        status, sub = self.desk.update_lease(
            "submit",
            {
                "source_sha256": src_sha,
                "kproof_sha256": kp_sha,
                "agent": {"model": "gpt-6.2-sol", "harness": "codex", "harness_version": "1.0"},
            },
            f"Bearer {lease_tok}",
            now + 20,
            auth=alice_pass,
        )
        self.assertEqual(status, 200)
        self.assertTrue(sub["private"])
        sub_id = sub["submission_id"]
        ticket = desk_mod.verify_upload_ticket(SECRET, sub["upload_ticket"], now + 25)
        self.assertIsNotNone(ticket)
        self.assertEqual(ticket["submission_id"], sub_id)
        self.assertEqual(ticket["github_uid"], 10001)

        # poll_desk.py pending() must NOT return pr=0 private submissions
        _, pend = self.desk.pending(now + 30)
        self.assertEqual(pend["pending"], [])

        stmt_sha = hashlib.sha256(SAMPLE_GAPS[0]["statement"].encode("utf-8")).hexdigest()
        status, authz = self.signed_call(
            "authorize",
            {
                "pr": 0,
                "head": sub_id,
                "handle": "alice",
                "gap": "L-goldbach-priv-1",
                "run_id": 501,
                "kind": "prove",
                "module": "Conjectures.Goldbach.PrivOne",
                "statement_sha256": stmt_sha,
            },
            now + 40,
        )
        self.assertEqual(status, 200)

        # Public activities while checking must NOT expose handle, pr, or submission_id
        with patch("deploy.desk.time.time", return_value=now + 45):
            pub = self.desk.public_status()
        checking_events = [e for e in pub["activities"] if e["kind"] == "checking"]
        self.assertEqual(len(checking_events), 1)
        self.assertNotIn("handle", checking_events[0])
        self.assertNotIn("pr", checking_events[0])
        self.assertNotIn("head_sha", checking_events[0])

        # Record private diagnostic and reject: public feed stays anonymous, private status shows detail
        self.signed_call(
            "record_diagnostic",
            {"gap": "L-goldbach-priv-1", "head": sub_id, "run_id": 501, "diagnostic": "REJECTED (statement): type mismatch"},
            now + 50,
        )
        with self.desk.transaction(write=True) as conn:
            with patch("deploy.desk.time.time", return_value=now + 55):
                self.desk.record_verdict(
                    {
                        "lemma_id": "L-goldbach-priv-1",
                        "verdict": "REJECTED",
                        "run_id": 501,
                        "run_attempt": 1,
                        "manifest": None,
                        "head_sha": sub_id,
                    },
                    conn,
                )
        with patch("deploy.desk.time.time", return_value=now + 60):
            pub_after = self.desk.public_status()
        rejected_events = [e for e in pub_after["activities"] if e["kind"] == "rejected"]
        self.assertEqual(len(rejected_events), 1)
        self.assertNotIn("handle", rejected_events[0])
        self.assertNotIn("head_sha", rejected_events[0])

        status, priv = self.desk.lease_status(f"Bearer {lease_tok}", now + 60)
        self.assertEqual(status, 200)
        self.assertEqual(priv["state"], "rejected")
        self.assertIn("type mismatch", priv["diagnostic"])
        self.assertEqual(priv["submission_id"], sub_id)

    def test_kernel_verified_timestamp_wins_first_acceptance_and_published_backfills_sha(self):
        now = 5000
        alice_pass = self.issue_pass("alice", 20001, now)
        bob_pass = self.issue_pass("bob", 20002, now)

        _, c_alice = self.desk.claim({"handle": "alice", "gap": "L-goldbach-priv-1"}, "198.51.100.11", now + 1, auth=alice_pass)
        _, c_bob = self.desk.claim({"handle": "bob", "gap": "L-goldbach-priv-1"}, "198.51.100.12", now + 2, auth=bob_pass)

        _, s_alice = self.desk.update_lease(
            "submit",
            {"source_sha256": "a" * 64, "kproof_sha256": "b" * 64, "agent": {"model": "gpt-6.2-sol", "harness": "codex"}},
            f"Bearer {c_alice['lease']['token']}",
            now + 10,
            auth=alice_pass,
        )
        _, s_bob = self.desk.update_lease(
            "submit",
            {"source_sha256": "c" * 64, "kproof_sha256": None, "agent": {"model": "claude-opus-5-5", "harness": "claude-code"}},
            f"Bearer {c_bob['lease']['token']}",
            now + 12,
            auth=bob_pass,
        )
        stmt_sha = hashlib.sha256(SAMPLE_GAPS[0]["statement"].encode("utf-8")).hexdigest()
        self.signed_call("authorize", {
            "pr": 0, "head": s_alice["submission_id"], "handle": "alice",
            "gap": "L-goldbach-priv-1", "run_id": 701, "kind": "prove",
            "module": "Conjectures.Goldbach.PrivOne", "statement_sha256": stmt_sha,
        }, now + 20)
        self.signed_call("authorize", {
            "pr": 0, "head": s_bob["submission_id"], "handle": "bob",
            "gap": "L-goldbach-priv-1", "run_id": 702, "kind": "prove",
            "module": "Conjectures.Goldbach.PrivOne", "statement_sha256": stmt_sha,
        }, now + 21)

        # Alice passes Stage-1 KProof at t = now + 25 (2s later!)
        status, kv = self.signed_call("kernel_verified", {
            "run_id": 701, "gap": "L-goldbach-priv-1", "head": s_alice["submission_id"],
        }, now + 25)
        self.assertEqual(status, 200)
        self.assertEqual(kv["kernel_verified_at"], now + 25)

        # Bob finishes Stage-2 earlier at t = now + 80, Alice finishes Stage-2 at t = now + 120
        with self.desk.transaction(write=True) as conn:
            conn.execute("CREATE TABLE IF NOT EXISTS verdicts (run_id INTEGER, attempt INTEGER, body BLOB, PRIMARY KEY (run_id, attempt))")
            for run_id, sub_id, fin in ((702, s_bob["submission_id"], now + 80), (701, s_alice["submission_id"], now + 120)):
                rec = {
                    "lemma_id": "L-goldbach-priv-1",
                    "verdict": "ACCEPTED",
                    "run_id": run_id,
                    "run_attempt": 1,
                    "head_sha": sub_id,
                    "manifest": {"rests_on": [{"module": "Conjectures.Goldbach.PrivOne", "sha256": "f" * 64}], "defs": []},
                }
                conn.execute("INSERT INTO verdicts VALUES (?, 1, ?)", (run_id, json.dumps(rec).encode()))
                with patch("deploy.desk.time.time", return_value=fin):
                    self.desk.record_verdict(rec, conn)

        # Alice wins points despite later finished_at because kernel_verified_at = now + 25 < now + 80!
        with patch("deploy.desk.time.time", return_value=now + 130):
            pub = self.desk.public_status()
        self.assertEqual(pub["rankings"]["all_time"][0]["handle"], "alice")
        self.assertEqual(pub["agent_rankings"]["models"][0]["name"], "gpt-6.2-sol")

        # Publish Alice's commit to main and verify backfill
        main_commit = "9" * 40
        status, pub_res = self.signed_call("record_published", {
            "run_id": 701,
            "gap": "L-goldbach-priv-1",
            "commit_sha": main_commit,
            "check_id": 888123,
        }, now + 135)
        self.assertEqual(status, 200)
        _, alice_status = self.desk.lease_status(f"Bearer {c_alice['lease']['token']}", now + 140)
        self.assertEqual(alice_status["published_sha"], main_commit)
        with self.desk.transaction() as conn:
            vbody = json.loads(conn.execute("SELECT body FROM verdicts WHERE run_id=701").fetchone()[0])
        self.assertEqual(vbody["head_sha"], main_commit)
        self.assertEqual(vbody["check_id"], 888123)

    def test_five_tier_strikes_level4_three_day_decay_and_no_nat_ip_collateral(self):
        t0 = 10_000
        bad_pass = self.issue_pass("sloppyuser", 90001, t0)
        labmate_pass = self.issue_pass("goodlabmate", 90002, t0)

        # Strikes 1 and 2: exempt warning only
        for expected_strike in (1, 2):
            status, res = self.signed_call("record_moderation_event", {
                "kind": "stage2_resource_limit",
                "handle": "sloppyuser",
                "github_uid": 90001,
                "detail": "timeout 124",
            }, t0 + expected_strike * 10)
            self.assertEqual(status, 200)
            self.assertEqual(res["strikes"], expected_strike)
            self.assertEqual(res["action"], "warn")
            self.assertFalse(res["throttled"])
            self.assertIsNone(self.desk.ban_status(90001, "sloppyuser", t0 + expected_strike * 10))

        # Strike 3: throttled (2-slot slow pool, no early kernel_verified_at)
        t_s3 = t0 + 100
        _, res3 = self.signed_call("record_moderation_event", {
            "kind": "stage2_resource_limit", "handle": "sloppyuser", "github_uid": 90001,
        }, t_s3)
        self.assertEqual(res3["strikes"], 3)
        self.assertEqual(res3["action"], "throttled")
        self.assertTrue(res3["throttled"])

        # After 1 day (86400s), Strike 3 decays by 1 back to 2 (no longer throttled)
        sinfo_after_1d = self.desk.strike_info(90001, "sloppyuser", t_s3 + 86400)
        self.assertEqual(sinfo_after_1d["strikes"], 2)
        self.assertFalse(sinfo_after_1d["throttled"])

        # Bring back to Strike 3, then Strike 4 (24h temp ban)
        t_s3b = t_s3 + 86500
        self.signed_call("record_moderation_event", {
            "kind": "stage2_resource_limit", "handle": "sloppyuser", "github_uid": 90001,
        }, t_s3b)
        # Also open an unsubmitted lease to verify Strike 4 revokes it
        c_status, _ = self.desk.claim({"handle": "sloppyuser", "gap": "L-goldbach-priv-2"}, "203.0.113.50", t_s3b + 5, auth=bad_pass)
        self.assertEqual(c_status, 201)

        t_s4 = t_s3b + 10
        _, res4 = self.signed_call("record_moderation_event", {
            "kind": "stage2_resource_limit", "handle": "sloppyuser", "github_uid": 90001,
        }, t_s4)
        self.assertEqual(res4["strikes"], 4)
        self.assertEqual(res4["action"], "temp_ban_24h")
        self.assertEqual(res4["expires_at"], t_s4 + 86400)

        # Banned actor blocked during 24h window
        b_status, b_err = self.desk.claim({"handle": "sloppyuser"}, "203.0.113.50", t_s4 + 60, auth=bad_pass)
        self.assertEqual(b_status, 403)
        self.assertEqual(b_err["error"], "account_banned")

        # Labmate on the EXACT SAME NAT IP 203.0.113.50 is NOT affected!
        g_status, _ = self.desk.claim({"handle": "goodlabmate", "gap": "L-goldbach-priv-1"}, "203.0.113.50", t_s4 + 60, auth=labmate_pass)
        self.assertEqual(g_status, 201)

        # CRITICAL: After 25 hours (ban expired, < 3 days), Strike 4 has NOT decayed yet!
        t_after_ban = t_s4 + 25 * 3600
        self.assertIsNone(self.desk.ban_status(90001, "sloppyuser", t_after_ban))
        self.assertEqual(self.desk.strike_info(90001, "sloppyuser", t_after_ban)["strikes"], 4)

        # Test 3-day decay calculation before triggering Strike 5: at +3 days, Strike 4 WOULD decay to 3
        self.assertEqual(self.desk.strike_info(90001, "sloppyuser", t_s4 + 3 * 86400)["strikes"], 3)
        self.assertEqual(self.desk.strike_info(90001, "sloppyuser", t_s4 + 6 * 86400)["strikes"], 0)

        # Offending again at +25h reaches Strike 5 -> PERMANENT BAN!
        _, res5 = self.signed_call("record_moderation_event", {
            "kind": "stage2_resource_limit", "handle": "sloppyuser", "github_uid": 90001,
        }, t_after_ban + 10)
        self.assertEqual(res5["strikes"], 5)
        self.assertEqual(res5["action"], "permanent_ban")
        self.assertIsNone(res5["expires_at"])

        # Even 365 days later, and even if UID 90001 renames GitHub handle to 'freshname', still permanently banned!
        renamed_pass = desk_mod.contributor_pass(SECRET, 90001, "freshname", t_after_ban + 400 * 86400)
        r_status, r_err = self.desk.claim(
            {"handle": "freshname"}, "198.51.100.99", t_after_ban + 365 * 86400, auth=renamed_pass
        )
        self.assertEqual(r_status, 403)
        self.assertTrue(r_err["permanent"])

        # Admin CLI ban_actor.py --unban lifts the permanent ban cleanly
        out = io.StringIO()
        with patch.object(sys, "argv", ["ban_actor.py", "--state-dir", str(self.state_dir), "--unban", "--uid", "90001"]), \
             contextlib.redirect_stdout(out):
            ban_actor.main()
        self.assertTrue(json.loads(out.getvalue())["unbanned"])
        self.assertIsNone(self.desk.ban_status(90001, "freshname", t_after_ban + 365 * 86400))

    def test_one_hit_tamper_permanent_ban_and_cli_local_guard(self):
        now = 30_000
        self.issue_pass("cheater", 77777, now)
        status, res = self.signed_call("record_moderation_event", {
            "kind": "tamper",
            "handle": "cheater",
            "github_uid": 77777,
            "detail": "REJECTED (sorry): theorem depends on sorryAx",
        }, now + 5)
        self.assertEqual(status, 200)
        self.assertEqual(res["action"], "permanent_ban")
        ban = self.desk.ban_status(77777, "cheater", now + 999_999)
        self.assertIsNotNone(ban)
        self.assertTrue(ban["permanent"])

        # CLI local_check_proof catches sorry, forbidden set_option, modulo %, and passes clean theorem
        gap = SAMPLE_GAPS[0]
        with self.assertRaisesRegex(SystemExit, 'REFUSED.*"sorry"'):
            cli.local_check_proof(b"import Mathlib\ntheorem Conjectures.Goldbach.PrivOne : True := by sorry\n", gap, ROOT)
        with self.assertRaisesRegex(SystemExit, "Nat.mod"):
            cli.local_check_proof(b"import Mathlib\ntheorem Conjectures.Goldbach.PrivOne : 5% 2 = 1 := rfl\n", gap, ROOT)
        cli.local_check_proof(
            "import Mathlib\nset_option maxHeartbeats 400000 in\ntheorem Conjectures.Goldbach.PrivOne : ∀ n : Nat, n = n := fun n => rfl\n".encode("utf-8"),
            gap,
            ROOT,
        )


if __name__ == "__main__":
    unittest.main()
