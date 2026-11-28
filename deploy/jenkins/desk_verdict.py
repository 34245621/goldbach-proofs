"""Send a previously persisted verdict to the Goldbach desk."""

import hashlib
import hmac
import json
import re
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

RETRY_HTTP_CODES = frozenset({502, 503, 504})
REASON = re.compile(r"[a-z0-9_]{1,64}")


class DeskRefused(ValueError):
    """The task desk deterministically refused authorization for this submission."""


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None


def open_with_retry(request, *, maximum=262144, timeout=25, attempts=3):
    opener = build_opener(NoRedirect())
    for attempt in range(1, attempts + 1):
        try:
            with opener.open(request, timeout=timeout) as response:
                return response.status, response.read(maximum + 1)
        except HTTPError as error:
            if error.code not in RETRY_HTTP_CODES or attempt == attempts:
                raise
        except (TimeoutError, URLError):
            if attempt == attempts:
                raise
        time.sleep(2 * attempt)


def signed_request(url, secret, payload):
    target = urlsplit(url)
    if target.scheme != "https" or not target.hostname or target.username is not None or target.fragment:
        raise ValueError("Expected an HTTPS verdict endpoint")
    if not secret or not isinstance(payload, bytes) or not 1 <= len(payload) <= 262144:
        raise ValueError("Expected a signing secret and a valid verdict payload")
    signature = hmac.new(secret, payload, hashlib.sha256).hexdigest()
    request = Request(url, payload, {
        "Content-Type": "application/json",
        "X-Goldbach-Signature": "sha256=" + signature,
    })
    status, data = open_with_retry(request)
    if status != 200 or len(data) > 262144:
        raise RuntimeError("Invalid signed Desk response")
    return json.loads(data)


def signed_post(url, secret, payload, expected):
    if signed_request(url, secret, payload) != expected:
        raise RuntimeError("Desk endpoint did not acknowledge the request")


def _post_authorize(url, secret, payload):
    try:
        signed_post(url.rstrip("/") + "/authorize", secret, payload, {"authorized": True})
    except HTTPError as error:
        if error.code == 409:
            reason = "conflict"
            try:
                parsed = json.loads(error.read(4096))
                candidate = parsed.get("error", "") if isinstance(parsed, dict) else ""
                if isinstance(candidate, str) and REASON.fullmatch(candidate):
                    reason = candidate
            except (OSError, ValueError, TypeError):
                pass
            raise DeskRefused(reason) from None
        raise


def precheck(url, secret, *, pr, head, handle, gap, run_id):
    payload = json.dumps({
        "pr": pr,
        "head": head,
        "handle": handle,
        "gap": gap,
        "run_id": run_id,
        "dry_run": True,
    }).encode()
    try:
        _post_authorize(url, secret, payload)
    except HTTPError as error:
        if error.code == 400:
            return False
        raise
    return True


def authorize(url, secret, *, pr, head, handle, gap, run_id, statement, kind="prove", module=None):
    payload = json.dumps({
        "pr": pr,
        "head": head,
        "handle": handle,
        "gap": gap,
        "run_id": run_id, "kind": kind, "module": module,
        "statement_sha256": hashlib.sha256(statement).hexdigest(),
    }).encode()
    _post_authorize(url, secret, payload)


def send_verdict(url, secret, payload):
    signed_post(url, secret, payload, {"status": "stored"})


def report_kernel_verified(url, secret, *, run_id, gap, head):
    payload = json.dumps({
        "run_id": run_id,
        "gap": gap,
        "head": head,
    }).encode()
    return signed_request(url.rstrip("/") + "/kernel-verified", secret, payload)


def report_diagnostic(url, secret, *, gap, head, diagnostic, run_id=None):
    body = {"gap": gap, "head": head, "diagnostic": str(diagnostic)[:8000]}
    if run_id is not None:
        body["run_id"] = run_id
    payload = json.dumps(body, ensure_ascii=False).encode("utf-8")
    return signed_request(url.rstrip("/") + "/diagnostic", secret, payload)


def report_moderation(url, secret, *, kind, handle, github_uid=None, run_id=None, gap=None, head=None, detail=""):
    body = {"kind": kind, "handle": handle, "detail": str(detail)[:1000]}
    if github_uid is not None:
        body["github_uid"] = github_uid
    if run_id is not None:
        body["run_id"] = run_id
    if gap is not None:
        body["gap"] = gap
    if head is not None:
        body["head"] = head
    payload = json.dumps(body, ensure_ascii=False).encode("utf-8")
    return signed_request(url.rstrip("/") + "/moderation-event", secret, payload)


def report_published(url, secret, *, run_id, gap, commit_sha, check_id=None):
    body = {"run_id": run_id, "gap": gap, "commit_sha": commit_sha}
    if check_id is not None:
        body["check_id"] = check_id
    payload = json.dumps(body).encode()
    return signed_request(url.rstrip("/") + "/published", secret, payload)
