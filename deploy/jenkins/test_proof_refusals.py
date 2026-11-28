import io
import json
import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
from urllib.error import HTTPError

from build_checks import enqueue_formal_checks, refusal_summary
from check_outbox import database
from desk_verdict import DeskRefused, precheck, signed_request
from formal_proof import judge
from desk_outbox import clear_active_job, drain, enqueue_runner_failures, initialize, mark_active_job
from prepare_proof import ProofRefused, generated_task, guard, report_guard_result
from site_runner import ActiveProofRegistry, check_proof, run_with_keepalive
from verify_proof import ProofCancelled, ProofRejected, verifier_manifest


class ProofRefusalTests(unittest.TestCase):
    def test_reconcile_failed_runner_then_publish_distinct_check(self):
        with tempfile.TemporaryDirectory() as directory, sqlite3.connect(":memory:") as jobs:
            jobs.executescript("""
                CREATE TABLE ci_jobs (id, kind, sha, pr, trigger);
                CREATE TABLE desk_runs (job_id, run_id);
                CREATE TABLE jenkins_dispatches (job_id, result);
                CREATE TABLE proof_refusals (job_id, reason);
                INSERT INTO ci_jobs VALUES (1, 'authoritative', 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 72, '8');
                INSERT INTO ci_jobs VALUES (2, 'authoritative', 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb', 73, '9');
                INSERT INTO desk_runs VALUES (1, 101), (2, 102);
                INSERT INTO jenkins_dispatches VALUES (1, 'FAILURE'), (2, 'FAILURE');
                INSERT INTO proof_refusals VALUES (2, 'source guard');
            """)
            initialize(jobs)
            enqueue_runner_failures(jobs, 100)
            enqueue_runner_failures(jobs, 100)
            self.assertEqual(jobs.execute("SELECT run FROM desk_outbox").fetchall(), [(101,)])
            with patch("desk_outbox.signed_post") as failure, patch("desk_outbox.send_verdict") as result:
                drain(jobs, "https://example.org/api/verdict", b"test")
                failure.assert_called_once()
                self.assertEqual(failure.call_args.args[0], "https://example.org/api/desk/check-failed")
                result.assert_not_called()
            outbox = database(Path(directory) / "checks.sqlite")
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT * FROM checks WHERE name LIKE '%Lean verdict'").fetchone()
            self.assertEqual(check["conclusion"], "failure")
            self.assertIn("before issuing a Lean verdict", check["summary"])
            outbox.close()

    def test_modulo_refusal_suggests_explicit_arithmetic_only(self):
        self.assertIn("Nat.mod p 30", refusal_summary('line 64: "p%" is not allowed in a proof file'))
        self.assertNotIn("Nat.mod", refusal_summary('line 12: "macro" is not allowed in a proof file'))

    def test_only_an_explicit_guard_refusal_is_reported(self):
        with self.assertRaisesRegex(ProofRefused, "line 64"):
            report_guard_result(subprocess.CompletedProcess(
                ["guard"], 1, 'REFUSED: line 64: "p%" is not allowed\nIgnored diagnostic\n',
            ))
        with self.assertRaises(subprocess.CalledProcessError):
            report_guard_result(subprocess.CompletedProcess(["guard"], 125, ""))

    def test_guard_raises_proof_refused_from_container_output(self):
        refused = subprocess.CompletedProcess(
            ["docker"], 1, 'REFUSED: line 10834: "set_option" is not allowed in a proof file\n',
        )
        with patch("prepare_proof.subprocess.run", return_value=refused) as run:
            with self.assertRaisesRegex(ProofRefused, 'line 10834: "set_option"'):
                guard(Path("/base"), Path("/work"), "imports", "/input/proof.lean")
        self.assertEqual(run.call_args.kwargs["stdout"], subprocess.PIPE)
        self.assertTrue(run.call_args.kwargs["text"])

    def test_reconcile_pre_runner_jenkins_failure_without_desk_run(self):
        with tempfile.TemporaryDirectory() as directory, sqlite3.connect(":memory:") as jobs:
            jobs.executescript("""
                CREATE TABLE ci_jobs (id INTEGER PRIMARY KEY, kind, sha, pr, trigger);
                CREATE TABLE desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL);
                CREATE TABLE jenkins_dispatches (job_id INTEGER PRIMARY KEY, result);
                INSERT INTO ci_jobs VALUES
                    (1, 'authoritative', '1111111111111111111111111111111111111111', 10, '1'),
                    (2, 'authoritative', '2222222222222222222222222222222222222222', 11, '2'),
                    (3, 'authoritative', '3333333333333333333333333333333333333333', 12, '3'),
                    (4, 'authoritative', '3333333333333333333333333333333333333333', 12, '4'),
                    (5, 'authoritative', '4444444444444444444444444444444444444444', 13, '5'),
                    (6, 'authoritative', '4444444444444444444444444444444444444444', 13, '6');
                INSERT INTO desk_runs VALUES (2, 50), (6, 200);
                INSERT INTO jenkins_dispatches VALUES
                    (1, 'FAILURE'),
                    (2, 'SUCCESS'),
                    (3, 'FAILURE'),
                    (4, 'FAILURE'),
                    (5, 'FAILURE'),
                    (6, 'SUCCESS');
            """)
            initialize(jobs)
            enqueue_runner_failures(jobs, 100)
            enqueue_runner_failures(jobs, 100)
            # Job 1 is older than the window, jobs 5/6 already have a desk_run for PR 13,
            # and jobs 3/4 share (PR 12, sha) so only one ERROR run is recorded.
            self.assertEqual(jobs.execute("SELECT job_id FROM desk_runs ORDER BY job_id").fetchall(),
                             [(2,), (4,), (6,)])
            self.assertEqual(jobs.execute("SELECT count(*) FROM desk_outbox").fetchone()[0], 1)
            outbox = database(Path(directory) / "checks.sqlite")
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT * FROM checks WHERE name LIKE '%Lean verdict'").fetchone()
            self.assertEqual(check["conclusion"], "failure")
            self.assertIn("before issuing a Lean verdict", check["summary"])
            outbox.close()

    def test_refusal_is_published_without_issuing_a_lean_verdict(self):
        with tempfile.TemporaryDirectory() as directory:
            jobs = sqlite3.connect(":memory:")
            jobs.execute("CREATE TABLE ci_jobs (id, kind, sha, pr, trigger)")
            jobs.execute("INSERT INTO ci_jobs VALUES (2, 'authoritative', ?, 3754, '7')", ("a" * 40,))
            jobs.execute("CREATE TABLE desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL)")
            outbox = database(Path(directory) / "checks.sqlite")
            with patch("formal_proof.prepare", side_effect=ProofRefused("line 64: token is not allowed")), \
                    patch("formal_proof.authorize") as authorize, patch("formal_proof.verify") as verify:
                with self.assertRaises(ProofRefused):
                    judge(jobs, None, 2, None, None, None, None, desk_url="", secret=b"")
            authorize.assert_not_called()
            verify.assert_not_called()
            self.assertEqual(jobs.execute("SELECT count(*) FROM desk_outbox").fetchone()[0], 0)
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT name, conclusion, summary FROM checks").fetchone()
            self.assertEqual(tuple(check)[:2], ("Goldbach CI / formal submission refused", "failure"))
            self.assertIn("before Lean ran", check["summary"])
            self.assertIn("line 64: token is not allowed", check["summary"])
            outbox.close()
            jobs.close()

    def test_desk_requests_retry_transient_timeout_and_502_but_not_409(self):
        class FakeResponse:
            status = 200

            def __init__(self, payload):
                self._payload = payload

            def __enter__(self):
                return self

            def __exit__(self, *args):
                return False

            def read(self, limit=-1):
                return self._payload[:limit] if limit >= 0 else self._payload

        class FakeOpener:
            def __init__(self, outcomes):
                self.outcomes = list(outcomes)
                self.calls = 0

            def open(self, request, timeout=None):
                self.calls += 1
                outcome = self.outcomes.pop(0)
                if isinstance(outcome, Exception):
                    raise outcome
                return outcome

        transient = FakeOpener([
            TimeoutError("timed out"),
            HTTPError("https://example.org", 502, "Bad Gateway", {}, io.BytesIO(b"")),
            FakeResponse(b'{"authorized":true}'),
        ])
        with patch("desk_verdict.build_opener", return_value=transient), patch("desk_verdict.time.sleep") as sleep:
            reply = signed_request("https://example.org/api/desk/authorize", b"secret", b"{}")
        self.assertEqual(reply, {"authorized": True})
        self.assertEqual(transient.calls, 3)
        self.assertEqual(sleep.call_count, 2)

        conflict = FakeOpener([
            HTTPError("https://example.org", 409, "Conflict", {}, io.BytesIO(b"")),
        ])
        with patch("desk_verdict.build_opener", return_value=conflict), patch("desk_verdict.time.sleep") as sleep:
            with self.assertRaises(HTTPError) as raised:
                signed_request("https://example.org/api/desk/authorize", b"secret", b"{}")
        self.assertEqual(raised.exception.code, 409)
        self.assertEqual(conflict.calls, 1)
        sleep.assert_not_called()

        task_reply = b'{"kind":"prove","gap":{"module":"Conjectures.Cuts.Task0123456789abcdef01234567"}}'
        task_opener = FakeOpener([TimeoutError("timed out"), FakeResponse(task_reply)])
        with patch("desk_verdict.build_opener", return_value=task_opener), patch("desk_verdict.time.sleep"):
            receipt = generated_task("Conjectures.Cuts.Task0123456789abcdef01234567")
        self.assertEqual(receipt["kind"], "prove")
        self.assertEqual(task_opener.calls, 2)

    def test_timeout_and_oom_become_proof_rejections_instead_of_infra_errors(self):
        for code, label in ((124, "timeout"), (137, "memory")):
            with self.subTest(code=code):
                with self.assertRaisesRegex(ProofRejected, label):
                    verifier_manifest(subprocess.CompletedProcess(["checklemma"], code, ""),
                                      "Conjectures.Goldbach.Test", b"", lambda _: b"")

    def test_active_formal_job_blocks_premature_error_reconciliation(self):
        from contextlib import closing
        with closing(sqlite3.connect(":memory:")) as jobs:
            jobs.executescript("""
                CREATE TABLE ci_jobs (id INTEGER PRIMARY KEY, kind, sha, pr, trigger);
                CREATE TABLE desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL);
                CREATE TABLE jenkins_dispatches (job_id INTEGER PRIMARY KEY, result);
                INSERT INTO ci_jobs VALUES (7, 'authoritative', '7777777777777777777777777777777777777777', 88, '10');
                INSERT INTO desk_runs VALUES (7, 500);
                INSERT INTO jenkins_dispatches VALUES (7, 'FAILURE');
            """)
            initialize(jobs)
            mark_active_job(jobs, 7, now=1_000)
            enqueue_runner_failures(jobs, 100, now=1_050)
            self.assertEqual(jobs.execute("SELECT count(*) FROM desk_outbox").fetchone()[0], 0)
            # Once the runner clears the active job without writing a verdict, reconciliation proceeds.
            clear_active_job(jobs, 7)
            enqueue_runner_failures(jobs, 100, now=1_060)
            row = jobs.execute("SELECT payload FROM desk_outbox WHERE run=500").fetchone()
            self.assertEqual(json.loads(row[0])["verdict"], "ERROR")

    def test_advisory_check_proof_runs_guard_only_and_supersedes_older_pr_containers(self):
        registry = ActiveProofRegistry()
        with patch("site_runner.ACTIVE_PROOFS", registry), \
             patch("site_runner.TRUSTED_BASE", Path(".")), \
             patch("site_runner.prepare") as prep, \
             patch("site_runner.subprocess.run") as docker_rm:
            with registry.track(42, "1" * 40) as (on_container, cancelled):
                on_container("goldbach-verify-old", True)
                self.assertEqual(check_proof(42, "2" * 40), 0)
                self.assertTrue(cancelled.is_set())
            prep.assert_called_once()
            docker_rm.assert_called_once_with(
                ["docker", "rm", "-f", "goldbach-verify-old"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15,
            )

    def test_advisory_check_proof_returns_one_on_guard_refusal(self):
        with patch("site_runner.TRUSTED_BASE", Path(".")), \
             patch("site_runner.prepare", side_effect=ProofRefused("sorry is not allowed")):
            self.assertEqual(check_proof(42, "2" * 40), 1)

    def test_keepalive_streams_running_frames_before_final_code(self):
        import time
        buf = io.BytesIO()
        code = run_with_keepalive(buf, True, lambda: (time.sleep(0.05), 0)[1], interval=0.01)
        self.assertEqual(code, 0)
        lines = buf.getvalue().splitlines()
        self.assertIn(b"running", lines[:-1])
        self.assertEqual(lines[-1], b"0")

    def test_desk_409_precheck_records_refusal_before_prepare_runs(self):
        from contextlib import closing
        with tempfile.TemporaryDirectory() as directory, closing(sqlite3.connect(":memory:")) as jobs:
            jobs.executescript("""
                CREATE TABLE ci_jobs (id INTEGER PRIMARY KEY, kind, sha, pr, trigger);
                CREATE TABLE desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL);
            """)
            sha = "a" * 40
            jobs.execute("INSERT INTO ci_jobs VALUES (9, 'authoritative', ?, 99, '555')", (sha,))
            app = Mock()
            app.request.return_value = {
                "issue_url": "https://api.github.com/repos/CGandGameEngineLearner/goldbach-proofs/issues/99",
                "user": {"type": "User", "login": "alice"},
                "body": "/goldbach-check L-goldbach-test",
            }
            pr_doc = {"state": "open", "head": {"sha": sha}, "user": {"login": "alice"}}
            err_body = io.BytesIO(b'{"error":"gap_already_proved"}')
            http_409 = HTTPError("https://desk.example/authorize", 409, "Conflict", {}, err_body)
            with patch("desk_verdict.signed_post", side_effect=http_409):
                with self.assertRaisesRegex(DeskRefused, "gap_already_proved"):
                    precheck("https://desk.example", b"secret", pr=99, head=sha,
                             handle="alice", gap="L-goldbach-test", run_id=1)

            with patch("formal_proof.pull_request", return_value=pr_doc), \
                 patch("formal_proof.precheck", side_effect=DeskRefused("gap_already_proved")), \
                 patch("formal_proof.prepare") as prep, \
                 patch("formal_proof.verify") as ver:
                with self.assertRaisesRegex(ProofRefused, "gap_already_proved"):
                    judge(jobs, app, 9, Path(directory), Path(directory), Path(directory), Path(directory),
                          desk_url="https://desk.example", secret=b"secret")
            prep.assert_not_called()
            ver.assert_not_called()
            outbox = database(Path(directory) / "checks.sqlite")
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT name, conclusion, summary FROM checks").fetchone()
            self.assertEqual(tuple(check)[:2], ("Goldbach CI / formal submission refused", "failure"))
            self.assertIn("task desk refused", check["summary"])
            self.assertIn("gap_already_proved", check["summary"])
            outbox.close()
