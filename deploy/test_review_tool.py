"""Local tests for the agent review commands; GitHub is always mocked."""
import contextlib
import io
import json
import runpy
import subprocess
import unittest
from unittest.mock import patch

from tools import goldbach


def pull_request(head="a" * 40, author="Alice", state="open", merged_at=None):
    return {
        "state": state, "merged_at": merged_at, "user": {"login": author},
        "head": {"sha": head},
        "base": {"ref": "main", "repo": {"full_name": goldbach.REPO, "default_branch": "main"}},
    }


def review_entry(body, author="Bob", head="a" * 40, state="COMMENTED"):
    return {"body": body, "user": {"login": author}, "commit_id": head, "state": state}


class ReviewToolTests(unittest.TestCase):
    def setUp(self):
        self.pr = pull_request()
        self.pages = [[]]
        self.calls = self.enterContext(patch.object(goldbach.subprocess, "check_output", side_effect=self.github))
        self.send = self.enterContext(patch.object(goldbach.subprocess, "run"))

    def github(self, args, **kwargs):
        if args == ("gh", "api", "user", "--jq", ".login"):
            return "bob"
        if args == ("gh", "api", f"repos/{goldbach.REPO}/pulls/7"):
            return json.dumps(self.pr)
        if args == ("gh", "api", f"repos/{goldbach.REPO}/pulls/7/reviews?per_page=100", "--paginate", "--slurp"):
            return json.dumps(self.pages)
        if args == ("gh", "api", f"repos/{goldbach.REPO}/commits/{'c' * 40}/comments?per_page=100", "--paginate", "--slurp"):
            return json.dumps(self.pages)
        if args == ("gh", "api", "repos/CGandGameEngineLearner/goldbach-proofs/commits/ccccccc"):
            return json.dumps({"sha": "c" * 40})
        if args == ("gh", "api", "repos/CGandGameEngineLearner/goldbach-proofs/commits?sha=main&path=lean%2FConjectures%2FGoldbach%2FDemo.lean&per_page=1"):
            return json.dumps([{"sha": "c" * 40}])
        if args == ("gh", "api", f"repos/{goldbach.REPO}/commits/{'c' * 40}/pulls"):
            return json.dumps([{"number": 7, "merge_commit_sha": "c" * 40}])
        raise AssertionError(f"Unexpected command: {args}")

    def main(self, *args):
        output = io.StringIO()
        with patch("sys.argv", ["goldbach.py", *args]), contextlib.redirect_stdout(output):
            goldbach.main()
        return output.getvalue()

    def test_body_boundaries_and_normalization(self):
        self.assertEqual(goldbach.normalize_review_body(" 字" * 25), " ".join(["字"] * 25))
        self.assertEqual(goldbach.normalize_review_body("字" * 50), "字" * 50)
        self.assertEqual(goldbach.normalize_review_body("  first   second  "), "first second")
        for body in ("由 a < b 且 c > d 推出界", "a<b 且 c>d", "/path", "https://example.com", "```lean"):
            with self.subTest(body=body):
                self.assertEqual(goldbach.normalize_review_body(body), body)
        for body in ("字" * 51, "", "   ", "\nabc", "abc\r", "a\tb", "a\x00b", "a\x7fb"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                goldbach.normalize_review_body(body)

    def test_command_captures_stderr(self):
        self.assertEqual(goldbach.command("gh", "api", "user", "--jq", ".login"), "bob")
        self.calls.assert_called_once_with(
            ("gh", "api", "user", "--jq", ".login"), encoding="utf-8", stderr=subprocess.PIPE
        )

    def test_entrypoint_preserves_command_failure_stderr(self):
        for stderr, expected in [("GitHub error details\nsecond line\n", "GitHub error details\nsecond line\n"),
                                 (b"invalid utf-8: \xff\n", "invalid utf-8: \ufffd\n")]:
            with self.subTest(stderr=stderr):
                self.calls.side_effect = subprocess.CalledProcessError(1, ("gh", "api"), stderr=stderr)
                output = io.StringIO()
                output.reconfigure = lambda **kwargs: None
                errors = io.StringIO()
                with patch("sys.argv", ["goldbach.py", "reviews", "7"]), \
                        contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors), \
                        self.assertRaises(SystemExit) as exit_error:
                    runpy.run_path(goldbach.__file__, run_name="__main__")
                self.assertEqual(errors.getvalue(), expected)
                self.assertEqual(str(exit_error.exception), "gh failed with exit status 1.")

    def test_dry_run_and_tags_no_commands(self):
        for options, expected in [
            ([], "[agent-review] finding"),
            (["--harness", "codex"], "[agent-review|codex] finding"),
            (["--model", "Model  X"], "[agent-review|model x] finding"),
            (["--model", "Model-X", "--harness", "codex"], "[agent-review|codex/model-x] finding"),
        ]:
            with self.subTest(options=options):
                self.assertEqual(self.main("review", "7", "--body", "finding", "--dry-run", *options).strip(), expected)
        self.calls.assert_not_called()
        self.send.assert_not_called()

    def test_invalid_options(self):
        for args in [("review", "0", "--body", "x", "--dry-run"),
                     ("review", "7", "--body", "x", "--model", "a" * 97, "--dry-run"),
                     ("review", "7", "--body", "x", "--model", "<bad>", "--dry-run"),
                     ("review", "7", "--body", "x", "--harness", "invalid", "--dry-run"),
                     ("reviews", "-1"), ("reviews", "7", "--limit", "0"),
                     ("reviews", "7", "--limit", "-5")]:
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                self.main(*args)
        self.calls.assert_not_called()
        self.send.assert_not_called()

    def test_self_review_allowed_and_duplicate_head_rejected(self):
        self.pr["user"]["login"] = "BOB"
        self.main("review", "7", "--body", "finding")
        self.send.assert_called_once()
        self.pages = [[], [review_entry("[agent-review] previous", author="BOB")]]
        with self.assertRaisesRegex(SystemExit, "already reviewed"):
            self.main("review", "7", "--body", "finding")
        self.send.assert_called_once()

    def test_new_head_and_dismissed_allow_review(self):
        self.pages = [[review_entry("[agent-review] old", head="b" * 40),
                       review_entry("[agent-review] dismissed", state="DISMISSED"),
                       review_entry("[agent-review] draft", state="PENDING")]]
        self.main("review", "7", "--body", "finding")
        self.send.assert_called_once_with(
            ["gh", "api", "--method", "POST", f"repos/{goldbach.REPO}/pulls/7/reviews",
             "-f", "commit_id=" + "a" * 40, "-f", "event=COMMENT", "-f", "body=[agent-review] finding"],
            check=True, stdout=subprocess.DEVNULL,
        )
        self.assertTrue(all(call.args[0][0] == "gh" for call in self.calls.call_args_list))

    def test_long_model_tag_round_trip_and_limit_boundaries(self):
        model = "a" * 96
        self.main("review", "7", "--body", "finding", "--model", model, "--harness", "claude-code")
        formatted = self.send.call_args.args[0][-1].removeprefix("body=")
        self.pages = [[review_entry(formatted)]]
        for limit in ("1", "200"):
            result = json.loads(self.main("reviews", "7", "--limit", limit))
            self.assertEqual(set(result), {"pr", "reviews"})
            self.assertEqual(result["reviews"][0]["tag"], "[agent-review|claude-code/" + model + "]")
            self.assertEqual(result["reviews"][0]["body"], "finding")

    def test_pr_states_allowed(self):
        for pr in (pull_request(state="closed"),
                   pull_request(state="closed", merged_at="2026-01-01"),
                   pull_request()):
            self.pr = pr
            self.main("review", "7", "--body", "finding")
        self.assertEqual(self.send.call_count, 3)

    def test_read_filters_flattens_truncates_and_limits(self):
        self.pages = [[review_entry("ordinary"), review_entry("[agent-review-fake] ignored"),
                       review_entry("[agent-review unclosed"),
                       review_entry("[agent-review] dismissed", state="DISMISSED"),
                       review_entry("[agent-review] draft", state="PENDING"),
                       review_entry("[agent-review] first")],
                      [review_entry("[agent-review|codex] " + "字" * 49 + "\nextra\x00stuff"),
                       review_entry("[agent-review] last\tline"), review_entry("[agent-review]   ")]]
        result = json.loads(self.main("reviews", "7", "--limit", "2"))
        self.assertEqual(set(result), {"pr", "reviews"})
        self.assertEqual(result["pr"], 7)
        self.assertEqual(len(result["reviews"]), 2)
        first, last = result["reviews"]
        self.assertEqual(first, {"author": "Bob", "commit": "a" * 40, "tag": "[agent-review|codex]", "body": "字" * 49})
        self.assertEqual(last["body"], "last line")
        all_reviews = json.loads(self.main("reviews", "7", "--limit", "50"))["reviews"]
        self.assertEqual([item["body"] for item in all_reviews], ["first", "字" * 49, "last line"])
        self.assertTrue(all(call.args[0][0] == "gh" for call in self.calls.call_args_list))
        self.send.assert_not_called()

    def test_commit_sha_review_and_read_round_trip(self):
        sha = "c" * 40
        self.main("review", sha, "--body", "reusable bound", "--model", "gpt-6.2-sol", "--harness", "codex")
        self.send.assert_called_once_with(
            ["gh", "api", "--method", "POST", f"repos/{goldbach.REPO}/commits/{sha}/comments",
             "-f", "body=[agent-review|codex/gpt-6.2-sol] reusable bound"],
            check=True, stdout=subprocess.DEVNULL,
        )
        self.pages = [[{"body": "[agent-review|codex/gpt-6.2-sol] reusable bound", "user": {"login": "bob"}}]]
        with self.assertRaisesRegex(SystemExit, "already reviewed this commit"):
            self.main("review", sha, "--body", "duplicate")
        read_res = json.loads(self.main("reviews", sha, "--limit", "5"))
        self.assertEqual(read_res, {
            "commit": sha,
            "reviews": [{
                "author": "bob",
                "commit": sha,
                "tag": "[agent-review|codex/gpt-6.2-sol]",
                "body": "reusable bound",
            }],
        })

    def test_module_and_lemma_id_and_short_sha_resolve_automatically(self):
        sha = "c" * 40
        # Short 7-char SHA resolves to full 40-char SHA
        self.main("review", "ccccccc", "--body", "short sha works")
        self.send.assert_called_once_with(
            ["gh", "api", "--method", "POST", f"repos/{goldbach.REPO}/commits/{sha}/comments",
             "-f", "body=[agent-review] short sha works"],
            check=True, stdout=subprocess.DEVNULL,
        )
        # Module name and Lemma ID resolve to main commit AND merge historical PR reviews + commit comments
        self.pages = [[{"body": "[agent-review|codex] note", "user": {"login": "alice"}}]]
        with patch.object(goldbach, "_lookup_gap_file", return_value="lean/Conjectures/Goldbach/Demo.lean"):
            by_gap = json.loads(self.main("reviews", "L-goldbach-demo", "--limit", "5"))
        self.assertEqual(by_gap["commit"], sha)
        self.assertEqual(by_gap["file"], "lean/Conjectures/Goldbach/Demo.lean")
        # Both historical PR #7 review and main commit comment match self.pages -> 2 combined entries
        self.assertEqual(len(by_gap["reviews"]), 2)

        by_mod = json.loads(self.main("reviews", "Conjectures.Goldbach.Demo", "--limit", "1"))
        self.assertEqual(by_mod["file"], "lean/Conjectures/Goldbach/Demo.lean")
        self.assertEqual(len(by_mod["reviews"]), 1)


if __name__ == "__main__":
    unittest.main()
