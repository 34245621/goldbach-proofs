import io
import json
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

from deploy import github_identity as identity


class GithubOwnershipTests(unittest.TestCase):
    def setUp(self):
        self.challenge = identity.new_challenge()
        self.gist = "a" * 32
        self.url = f"https://gist.github.com/Example/{self.gist}"
        self.file = {"truncated": False, "content": identity.proof_text(self.challenge, "Example")}
        self.owner = {"id": 871, "type": "User", "login": "Example"}
        self.data = {"id": self.gist, "owner": self.owner, "files": {identity.PROOF_FILENAME: self.file}}

    def verify(self, gist=None):
        with patch.object(identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(self.data).encode())
            result = identity.verify_gist(gist or self.url, self.challenge, "example")
            req = opener.return_value.open.call_args.args[0]
            self.assertEqual(req.full_url, f"https://api.github.com/gists/{self.gist}")
            self.assertNotIn("Authorization", req.headers)
            return result

    def test_exact_challenge_and_user_for_web_and_cli(self):
        self.assertEqual(self.verify(), (871, "example"))
        self.file["content"] += "\r\n"
        self.assertEqual(self.verify(self.gist), (871, "example"))

    def test_wrong_owner_challenge_and_truncation(self):
        for obj, key, invalid in (
            (self.owner, "login", "impostor"),
            (self.owner, "id", True),
            (self.owner, "type", "Bot"),
            (self.file, "truncated", True),
            (self.file, "content", identity.proof_text(identity.new_challenge(), "Example")),
            (self.data, "id", "b" * 32),
        ):
            with self.subTest(key=key), patch.dict(obj, {key: invalid}):
                with self.assertRaises(identity.GithubProofError) as caught:
                    self.verify()
                self.assertEqual(caught.exception.status, 422)

    def test_untrusted_url_never_fetched(self):
        for url in ("https://gist.github.com.example.org/" + self.gist, "https://example.org/" + self.gist,
                    "https://gist.github.com@example.org/" + self.gist, self.url + "?v=2",
                    "http://gist.github.com/Example/" + self.gist, self.gist + "/../../other"):
            with self.subTest(url=url), patch.object(identity.urllib.request, "build_opener") as opener:
                with self.assertRaises(identity.GithubProofError) as caught:
                    identity.verify_gist(url, self.challenge, "example")
                self.assertEqual(caught.exception.status, 400)
                opener.assert_not_called()

    def test_upstream_failures_leave_challenge_retryable(self):
        for http_code, status in ((403, 503), (404, 422), (429, 503), (500, 503), (302, 503)):
            with self.subTest(http_code=http_code), patch.object(identity.urllib.request, "build_opener") as opener:
                opener.return_value.open.side_effect = HTTPError(self.url, http_code, "", {}, None)
                with self.assertRaises(identity.GithubProofError) as caught:
                    identity.verify_gist(self.gist, self.challenge, "Example")
                self.assertEqual(caught.exception.status, status)

    def test_lease_recovery_purpose_is_domain_separated(self):
        recover_text = identity.proof_text(self.challenge, "Example", purpose="lease_recover")
        self.assertNotEqual(recover_text, self.file["content"])
        with patch.object(identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(self.data).encode())
            with self.assertRaises(identity.GithubProofError) as caught:
                identity.verify_gist(self.url, self.challenge, "example", purpose="lease_recover")
            self.assertEqual(caught.exception.status, 422)

        self.file["content"] = recover_text
        with patch.object(identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(self.data).encode())
            self.assertEqual(
                identity.verify_gist(self.url, self.challenge, "example", purpose="lease_recover"),
                (871, "example"),
            )
        with patch.object(identity.urllib.request, "build_opener") as opener:
            opener.return_value.open.return_value = io.BytesIO(json.dumps(self.data).encode())
            with self.assertRaises(identity.GithubProofError) as caught:
                identity.verify_gist(self.url, self.challenge, "example", purpose="zhihu_link")
            self.assertEqual(caught.exception.status, 422)
