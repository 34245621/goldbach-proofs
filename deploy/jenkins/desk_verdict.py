"""Send a previously persisted verdict to the Goldbach desk."""

import hashlib
import hmac
import json
import time
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener

RETRY_HTTP_CODES = frozenset({502, 503, 504})


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


def authorize(url, secret, *, pr, head, handle, gap, run_id, statement, kind="prove", module=None):
    payload = json.dumps({
        "pr": pr,
        "head": head,
        "handle": handle,
        "gap": gap,
        "run_id": run_id, "kind": kind, "module": module,
        "statement_sha256": hashlib.sha256(statement).hexdigest(),
    }).encode()
    signed_post(url.rstrip("/") + "/authorize", secret, payload, {"authorized": True})


def send_verdict(url, secret, payload):
    signed_post(url, secret, payload, {"status": "stored"})