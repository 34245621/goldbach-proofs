import hashlib
import json
import sqlite3
import unittest
from tempfile import TemporaryDirectory
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

from merge_proofs import REPO, SkipMerge, drain, git_blob, merge, prune_snapshots


class MergeProofTests(unittest.TestCase):
    head = "1" * 40
    main = "2" * 40
    merged = "3" * 40
    module = "Conjectures.Goldbach.Test"
    file = "lean/Conjectures/Goldbach/Test.lean"
    proof = b"verified proof bytes"

    def setUp(self):
        root = Path(self.enterContext(TemporaryDirectory()))
        self.base = root / "base"
        research = self.base / "research"
        research.mkdir(parents=True)
        gap = {"id": "L-test", "file": self.file, "module": self.module}
        (research / "gaps.json").write_text(json.dumps({"gaps": [gap]}))
        (research / "problems.json").write_text("{}")
        self.record = {
            "lemma_id": gap["id"], "head_sha": self.head, "verdict": "ACCEPTED",
            "manifest": {"rests_on": [
                {"module": self.module, "sha256": hashlib.sha256(self.proof).hexdigest()},
            ], "defs": []},
        }
        self.pr = {"state": "open", "draft": False, "mergeable": True, "merged": False, "changed_files": 1,
                   "head": {"sha": self.head},
                   "base": {"ref": "main", "sha": self.main, "repo": {"full_name": REPO.removeprefix("/repos/")}}}

    def test_merge_uses_verified_head_and_squash(self):
        app = Mock()
        current_main = {"object": {"sha": "4" * 40}}
        app.request.side_effect = [[{"filename": self.file, "status": "added"}],
                                   current_main, current_main,
                                   {"merged": True, "sha": self.merged}]
        # GitHub may still be computing mergeability. The SHA-bound merge endpoint
        # can decide after the worker has checked the files and dependency hashes.
        with patch("merge_proofs.pull_request", return_value=self.pr | {"mergeable": None}), \
             patch("merge_proofs.revision_tree", return_value={}) as tree, \
             patch("merge_proofs.verify_dependency"), \
             patch("merge_proofs.metadata", return_value={"sha": git_blob(self.proof)}), \
             patch("merge_proofs.proven_content", return_value=self.proof):
            self.assertEqual(merge(app, 55, self.head, self.record, self.base),
                             (self.merged, self.file, self.proof))
        app.request.assert_called_with("PUT", REPO + "/pulls/55/merge",
                                       {"sha": self.head, "merge_method": "squash"})
        tree.assert_called_once_with(app, current_main["object"]["sha"])

    def test_generated_modules_follow_the_official_kind_and_head(self):
        for kind, prefix in (("prove", "Task"), ("cut", "Cut"), ("refute", "Refute")):
            module = "Conjectures.Cuts." + prefix + "a" * 24
            path = "lean/" + module.replace(".", "/") + ".lean"
            record = dict(self.record, kind=kind, module=module, manifest={
                "rests_on": [{"module": module, "sha256": hashlib.sha256(self.proof).hexdigest()}], "defs": []})
            app = Mock()
            app.request.return_value = {"object": {"sha": self.main}}
            with self.subTest(kind=kind), patch("merge_proofs.pull_request", return_value={
                    **self.pr, "merged": True, "merge_commit_sha": self.merged}), patch(
                    "merge_proofs.proven_content", return_value=self.proof) as content, patch(
                    "merge_proofs.metadata", return_value={"sha": git_blob(self.proof)}):
                self.assertEqual(merge(app, 55, self.head, record, self.base), (self.merged, path, self.proof))
                self.assertEqual(content.call_args.args[1], path)
                with self.assertRaises(SkipMerge):
                    merge(app, 55, self.head, dict(record, kind="refute" if kind == "cut" else "cut"), self.base)

    def test_existing_path_on_main_blocks_old_pull_request(self):
        app = Mock()
        app.request.side_effect = [[{"filename": self.file, "status": "added"}],
                                   {"object": {"sha": "4" * 40}}]
        with patch("merge_proofs.pull_request", return_value=self.pr), \
             patch("merge_proofs.revision_tree", return_value={self.file: {}}), \
             self.assertRaisesRegex(SkipMerge, "already exists on main"):
            merge(app, 55, self.head, self.record, self.base)
        self.assertTrue(all(call.args[0] == "GET" for call in app.request.call_args_list))

    def test_changed_head_and_extra_files_never_merge(self):
        for pr, extra_files in ((self.pr | {"head": {"sha": self.merged}}, []),
                                (self.pr | {"changed_files": 2}, [{"filename": self.file},
                                                                {"filename": "lakefile.toml"}])):
            with self.subTest(pr=pr):
                app = Mock()
                app.request.return_value = extra_files
                with patch("merge_proofs.pull_request", return_value=pr), self.assertRaises(SkipMerge):
                    merge(app, 55, self.head, self.record, self.base)
                self.assertTrue(all(call.args[0] == "GET" for call in app.request.call_args_list))

    def test_only_delivered_official_success_enters_queue_once(self):
        db = sqlite3.connect(":memory:")
        self.addCleanup(db.close)
        db.executescript("""
            CREATE TABLE ci_jobs (id, pr, sha, kind);
            CREATE TABLE desk_runs (job_id, run_id);
            CREATE TABLE desk_outbox (run, attempt, payload, delivered);
            CREATE TABLE jenkins_dispatches (job_id, result);
        """)
        for number, kind, verdict, delivered, result in (
            (1, "authoritative", "ACCEPTED", 1, "SUCCESS"),
            (2, "authoritative", "ACCEPTED", 0, "SUCCESS"),
            (3, "advisory", "ACCEPTED", 1, "SUCCESS"),
            (4, "authoritative", "REJECTED", 1, "FAILURE"),
            (5, "authoritative", "ACCEPTED", 1, "ABORTED"),
        ):
            db.execute("INSERT INTO ci_jobs VALUES (?, ?, ?, ?)", (number, number + 50, self.head, kind))
            db.execute("INSERT INTO desk_runs VALUES (?, ?)", (number, number))
            db.execute("INSERT INTO desk_outbox VALUES (?, 1, ?, ?)",
                       (number, json.dumps(self.record | {"verdict": verdict}), delivered))
            db.execute("INSERT INTO jenkins_dispatches VALUES (?, ?)", (number, result))
        store = MagicMock()
        (store / "current").resolve.return_value = self.base
        with patch("merge_proofs.merge", return_value=(self.merged, self.file, self.proof)) as action, \
             patch("merge_proofs.publish_source") as publish:
            drain(db, Mock(), store, 1)
            drain(db, Mock(), store, 1)
        self.assertEqual(action.call_count, 1)
        self.assertEqual(action.call_args.args[1], 51)
        publish.assert_called_once_with(store, self.base, self.merged, self.file, self.proof)

    def test_prune_snapshots_preserves_current_recent_and_young_directories(self):
        store = Path(self.enterContext(TemporaryDirectory()))
        now = 1_700_000_000

        def make_snapshot(idx, age):
            folder = store / f"{idx:040x}-stage-snap{idx}"
            folder.mkdir()
            (folder / "marker").write_text("ok")
            mtime = now - age
            import os
            os.utime(folder, (mtime, mtime))
            return folder

        oldest_active = make_snapshot(1, 20_000)
        (store / "current").symlink_to(oldest_active)
        expired_a = make_snapshot(2, 19_000)
        expired_b = make_snapshot(3, 18_000)
        young_beyond_keep = make_snapshot(4, 1_800)  # rank 3, but < 3h window: must be preserved
        recent_a = make_snapshot(5, 1_200)  # rank 2: preserved by keep_recent=2
        recent_b = make_snapshot(6, 600)    # rank 1: preserved by keep_recent=2
        in_flight_stage = store / "stage-inflight"
        in_flight_stage.mkdir()

        removed = prune_snapshots(store, keep_recent=2, min_age_seconds=10_800, max_delete=1, now=now)
        self.assertEqual(removed, 1)
        self.assertFalse(expired_a.exists())
        self.assertTrue(expired_b.exists())  # respected max_delete=1
        self.assertTrue(oldest_active.exists())  # current symlink target never deleted

        removed_second = prune_snapshots(store, keep_recent=2, min_age_seconds=10_800, max_delete=5, now=now)
        self.assertEqual(removed_second, 1)
        self.assertFalse(expired_b.exists())
        self.assertTrue(young_beyond_keep.exists())
        self.assertTrue(recent_a.exists())
        self.assertTrue(recent_b.exists())
        self.assertTrue(in_flight_stage.exists())
