"""Receive signed GitHub App events and private proof bundles for the Jenkins dispatcher."""

import base64
import gzip
import hashlib
import hmac
import json
import logging
import os
import re
import shutil
import sqlite3
import struct
import tempfile
import time
import zlib
from contextlib import closing
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import event_jobs

REPOSITORY = "CGandGameEngineLearner/goldbach-proofs"
INSTALLATION = 186036038
EVENTS = {"pull_request", "issue_comment", "push", "check_run"}
MAX_BODY = 25 * 1024 * 1024
MAX_UPLOAD_BYTES = 128 * 1024 * 1024
MAX_LEAN_BYTES = 2 * 1024 * 1024
MAX_KPROOF_UNCOMPRESSED_BYTES = int(os.environ.get("GOLDBACH_MAX_KPROOF_BYTES", str(512 * 1024 * 1024)))
UPLOAD_CHUNK_BYTES = 65536
UPLOAD_CHUNK_TIMEOUT = 30
UPLOAD_TOTAL_TIMEOUT = 300
BUNDLE_MAGIC = b"GBDL\x01"
KPROOF_MAGIC = b"KPRF\x01"
SUBMISSION_ID = re.compile(r"[0-9a-f]{40}", re.ASCII)
SHA256_HEX = re.compile(r"[0-9a-f]{64}", re.ASCII)


class BundleError(ValueError):
    def __init__(self, status, code):
        super().__init__(code)
        self.status = status
        self.code = code


def verify_upload_ticket(secret, token, now):
    if not secret or not isinstance(token, str) or "." not in token or len(token) > 60 * 1024:
        return None
    encoded, supplied_sig = token.rsplit(".", 1)
    if not re.fullmatch(r"[A-Za-z0-9_-]+", encoded) or not re.fullmatch(r"[a-f0-9]{64}", supplied_sig):
        return None
    expected_sig = hmac.new(secret, encoded.encode("ascii"), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(supplied_sig, expected_sig):
        return None
    padding = "=" * (-len(encoded) % 4)
    try:
        raw = base64.urlsafe_b64decode(encoded + padding)
        if raw.startswith(b"Z"):
            decoder = zlib.decompressobj()
            raw = decoder.decompress(raw[1:], 1024 * 1024)
            if not decoder.eof or decoder.unused_data:
                return None
        data = json.loads(raw)
    except (ValueError, UnicodeError, zlib.error):
        return None
    if (not isinstance(data, dict)
            or data.get("v") != 1
            or type(data.get("expires_at")) is not int
            or data["expires_at"] <= now
            or not isinstance(data.get("submission_id"), str)
            or not SUBMISSION_ID.fullmatch(data["submission_id"])
            or not isinstance(data.get("source_sha256"), str)
            or not SHA256_HEX.fullmatch(data["source_sha256"])):
        return None
    kproof_hash = data.get("kproof_sha256")
    if kproof_hash is not None and (not isinstance(kproof_hash, str) or not SHA256_HEX.fullmatch(kproof_hash)):
        return None
    return data


def pack_submission_bundle(lean_bytes, kproof_bytes=None, *, compresslevel=6):
    kproof = b"" if kproof_bytes is None else bytes(kproof_bytes)
    frame = (
        BUNDLE_MAGIC
        + struct.pack("<I", len(lean_bytes))
        + bytes(lean_bytes)
        + struct.pack("<I", len(kproof))
        + kproof
    )
    return gzip.compress(frame, compresslevel=compresslevel, mtime=0)


class _ChunkedBodyReader:
    """Decode HTTP/1.1 Transfer-Encoding: chunked streams with a strict byte ceiling."""

    def __init__(self, rfile, max_bytes=MAX_UPLOAD_BYTES):
        self._rfile = rfile
        self._max_bytes = max_bytes
        self._total = 0
        self._chunk_rem = 0
        self._eof = False

    def read(self, size=UPLOAD_CHUNK_BYTES):
        if self._eof or size <= 0:
            return b""
        while self._chunk_rem == 0:
            line = self._rfile.readline(4096)
            if not line or not line.endswith(b"\r\n"):
                raise BundleError(400, "truncated_upload")
            header = line[:-2].split(b";", 1)[0].strip()
            if not header or len(header) > 10:
                raise BundleError(400, "invalid_chunked_encoding")
            try:
                chunk_len = int(header, 16)
            except ValueError as exc:
                raise BundleError(400, "invalid_chunked_encoding") from exc
            if chunk_len < 0:
                raise BundleError(400, "invalid_chunked_encoding")
            if chunk_len == 0:
                # Consume optional trailer headers terminated by an empty CRLF line.
                for _ in range(64):
                    trailer = self._rfile.readline(4096)
                    if not trailer or not trailer.endswith(b"\r\n"):
                        raise BundleError(400, "truncated_upload")
                    if trailer == b"\r\n":
                        self._eof = True
                        return b""
                raise BundleError(400, "invalid_chunked_encoding")
            if self._total + chunk_len > self._max_bytes:
                raise BundleError(413, "bundle_too_large")
            self._chunk_rem = chunk_len

        want = min(size, self._chunk_rem)
        data = self._rfile.read(want)
        if not data:
            raise BundleError(400, "truncated_upload")
        self._chunk_rem -= len(data)
        self._total += len(data)
        if self._chunk_rem == 0:
            crlf = self._rfile.read(2)
            if crlf != b"\r\n":
                raise BundleError(400, "invalid_chunked_encoding")
        return data


def stream_unpack_bundle(rfile, content_length, ticket, dest_dir, *,
                         chunk_timeout=UPLOAD_CHUNK_TIMEOUT, max_seconds=UPLOAD_TOTAL_TIMEOUT,
                         set_timeout=None):
    if content_length is not None and not 1 <= content_length <= MAX_UPLOAD_BYTES:
        raise BundleError(413, "bundle_too_large")
    expected_lean_sha = ticket["source_sha256"]
    expected_kproof_sha = ticket.get("kproof_sha256")

    decompressor = zlib.decompressobj(16 + zlib.MAX_WBITS)
    buf = bytearray()
    state = "magic"
    lean_remaining = 0
    kproof_remaining = 0
    lean_hasher = hashlib.sha256()
    kproof_hasher = hashlib.sha256()
    kproof_prefix = bytearray()
    lean_file = None
    kproof_file = None
    deadline = time.monotonic() + max_seconds
    remaining_compressed = content_length
    total_compressed = 0

    try:
        while remaining_compressed is None or remaining_compressed > 0:
            if time.monotonic() > deadline:
                raise BundleError(408, "upload_timeout")
            if set_timeout is not None:
                set_timeout(chunk_timeout)
            read_size = UPLOAD_CHUNK_BYTES if remaining_compressed is None else min(UPLOAD_CHUNK_BYTES, remaining_compressed)
            try:
                chunk = rfile.read(read_size)
            except TimeoutError as exc:
                raise BundleError(408, "upload_timeout") from exc
            if not chunk:
                if remaining_compressed is None:
                    break
                raise BundleError(400, "truncated_upload")
            total_compressed += len(chunk)
            if total_compressed > MAX_UPLOAD_BYTES:
                raise BundleError(413, "bundle_too_large")
            if remaining_compressed is not None:
                remaining_compressed -= len(chunk)
            try:
                # Bound per-chunk decompression output to prevent zip bombs from spiking RAM.
                uncompressed = decompressor.decompress(chunk, 4 * 1024 * 1024)
            except zlib.error as exc:
                raise BundleError(400, "invalid_gzip") from exc

            pending = [uncompressed]
            while decompressor.unconsumed_tail:
                if time.monotonic() > deadline:
                    raise BundleError(408, "upload_timeout")
                try:
                    more = decompressor.decompress(decompressor.unconsumed_tail, 4 * 1024 * 1024)
                except zlib.error as exc:
                    raise BundleError(400, "invalid_gzip") from exc
                if more:
                    pending.append(more)

            for piece in pending:
                if not piece:
                    continue
                buf.extend(piece)
                while True:
                    if state == "magic":
                        if len(buf) < 9:
                            break
                        if bytes(buf[:5]) != BUNDLE_MAGIC:
                            raise BundleError(400, "invalid_bundle_magic")
                        lean_len, = struct.unpack("<I", buf[5:9])
                        del buf[:9]
                        if not 1 <= lean_len <= MAX_LEAN_BYTES:
                            raise BundleError(413, "invalid_lean_size")
                        lean_remaining = lean_len
                        lean_file = (dest_dir / "proof.lean").open("wb")
                        state = "lean"
                    elif state == "lean":
                        if not buf:
                            break
                        take = min(len(buf), lean_remaining)
                        mv = memoryview(buf)[:take]
                        lean_file.write(mv)
                        lean_hasher.update(mv)
                        mv.release()
                        del buf[:take]
                        lean_remaining -= take
                        if lean_remaining == 0:
                            lean_file.close()
                            lean_file = None
                            state = "kproof_header"
                    elif state == "kproof_header":
                        if len(buf) < 4:
                            break
                        kproof_len, = struct.unpack("<I", buf[:4])
                        del buf[:4]
                        if expected_kproof_sha is None:
                            if kproof_len != 0:
                                raise BundleError(400, "unexpected_kproof")
                            state = "done"
                        else:
                            if not 5 <= kproof_len <= MAX_KPROOF_UNCOMPRESSED_BYTES:
                                raise BundleError(413, "invalid_kproof_size")
                            kproof_remaining = kproof_len
                            kproof_file = (dest_dir / "proof.kproof").open("wb")
                            state = "kproof"
                    elif state == "kproof":
                        if not buf:
                            break
                        take = min(len(buf), kproof_remaining)
                        mv = memoryview(buf)[:take]
                        if len(kproof_prefix) < 5:
                            need = 5 - len(kproof_prefix)
                            kproof_prefix.extend(mv[:need])
                            if len(kproof_prefix) == 5 and bytes(kproof_prefix) != KPROOF_MAGIC:
                                mv.release()
                                raise BundleError(400, "invalid_kproof_magic")
                        kproof_file.write(mv)
                        kproof_hasher.update(mv)
                        mv.release()
                        del buf[:take]
                        kproof_remaining -= take
                        if kproof_remaining == 0:
                            kproof_file.close()
                            kproof_file = None
                            state = "done"
                    elif state == "done":
                        if buf:
                            raise BundleError(400, "trailing_bundle_bytes")
                        break

        try:
            tail = decompressor.flush()
        except zlib.error as exc:
            raise BundleError(400, "invalid_gzip") from exc
        if total_compressed == 0 or tail or not decompressor.eof or decompressor.unused_data or state != "done" or buf:
            raise BundleError(400, "incomplete_bundle")
    finally:
        if lean_file is not None:
            lean_file.close()
        if kproof_file is not None:
            kproof_file.close()

    if lean_hasher.hexdigest() != expected_lean_sha:
        raise BundleError(422, "source_sha256_mismatch")
    if expected_kproof_sha is not None and kproof_hasher.hexdigest() != expected_kproof_sha:
        raise BundleError(422, "kproof_sha256_mismatch")


class Receiver(BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path != "/github/webhook":
            self.send_error(404)
            return
        self.connection.settimeout(10)
        size = self.headers.get("Content-Length", "")
        if not re.fullmatch(r"[0-9]{1,8}", size) or not 0 < int(size) <= MAX_BODY:
            self.send_error(413)
            return
        try:
            raw = self.rfile.read(int(size))
        except TimeoutError:
            self.send_error(408)
            return
        if len(raw) != int(size):
            self.send_error(400)
            return
        expected = "sha256=" + hmac.new(self.server.secret, raw, hashlib.sha256).hexdigest()
        supplied = self.headers.get("X-Hub-Signature-256", "")
        if not supplied.isascii() or not hmac.compare_digest(expected, supplied):
            self.send_error(401)
            return

        event = self.headers.get("X-GitHub-Event", "")
        delivery = self.headers.get("X-GitHub-Delivery", "")
        if event not in EVENTS:
            self.respond(204)
            return
        if not re.fullmatch(r"[0-9a-fA-F]{8}(?:-[0-9a-fA-F]{4}){3}-[0-9a-fA-F]{12}", delivery):
            self.send_error(400)
            return
        try:
            payload = json.loads(raw)
            repository = payload["repository"]["full_name"]
            installation = payload["installation"]["id"]
        except (UnicodeError, ValueError, TypeError, KeyError):
            self.send_error(400)
            return
        if repository != REPOSITORY or installation != INSTALLATION:
            self.send_error(403)
            return
        try:
            with closing(sqlite3.connect(self.server.database)) as db, db:
                inserted = db.execute(
                    "INSERT INTO deliveries (id,event,body) VALUES (?,?,?) ON CONFLICT(id) DO NOTHING",
                    (delivery.lower(), event, raw),
                ).rowcount
                if not inserted:
                    previous = db.execute(
                        "SELECT event,body FROM deliveries WHERE id=?", (delivery.lower(),),
                    ).fetchone()
                    if previous != (event, raw):
                        self.send_error(409)
                        return
        except sqlite3.Error as error:
            logging.warning("Webhook queue write failed: %s", error)
            self.send_error(503)
            return
        self.respond(202)

    def do_PUT(self):
        if self.path != "/submissions/upload":
            self.send_error(404)
            return
        desk_secret = getattr(self.server, "desk_secret", None)
        submissions_dir = getattr(self.server, "submissions_dir", None)
        if not desk_secret or submissions_dir is None:
            self.respond_json(503, {"error": "upload_receiver_unconfigured"})
            return
        now = int(time.time())
        ticket_header = self.headers.get("X-Goldbach-Upload-Ticket", "")
        ticket = verify_upload_ticket(desk_secret, ticket_header, now)
        if ticket is None:
            self.respond_json(401, {"error": "invalid_upload_ticket"})
            return
        size_header = self.headers.get("Content-Length", "").strip()
        transfer_enc = self.headers.get("Transfer-Encoding", "").lower()
        if not size_header and "chunked" in {part.strip() for part in transfer_enc.split(",")}:
            body_stream = _ChunkedBodyReader(self.rfile, MAX_UPLOAD_BYTES)
            content_length = None
        else:
            if not re.fullmatch(r"[0-9]{1,10}", size_header) or not 1 <= int(size_header) <= MAX_UPLOAD_BYTES:
                self.respond_json(413, {"error": "bundle_too_large"})
                return
            body_stream = self.rfile
            content_length = int(size_header)

        submission_id = ticket["submission_id"]
        submissions_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        final_dir = submissions_dir / submission_id
        fast = bool(ticket.get("kproof_sha256")) and not bool(ticket.get("throttled"))
        trigger = f"bundle:{'fast' if fast else 'slow'}:{submission_id}"

        stage_dir = Path(tempfile.mkdtemp(prefix=f".stage-{submission_id[:12]}-", dir=submissions_dir))
        os.chmod(stage_dir, 0o700)
        try:
            stream_unpack_bundle(
                body_stream,
                content_length,
                ticket,
                stage_dir,
                set_timeout=self.connection.settimeout,
            )
            (stage_dir / "ticket.json").write_text(
                json.dumps(ticket, ensure_ascii=False, sort_keys=True),
                encoding="utf-8",
            )
            os.chmod(stage_dir / "proof.lean", 0o600)
            if (stage_dir / "proof.kproof").exists():
                os.chmod(stage_dir / "proof.kproof", 0o600)
            os.chmod(stage_dir / "ticket.json", 0o600)
            if not final_dir.exists():
                try:
                    stage_dir.rename(final_dir)
                except FileExistsError:
                    pass
        except BundleError as exc:
            self.respond_json(exc.status, {"error": exc.code})
            return
        finally:
            if stage_dir.exists():
                shutil.rmtree(stage_dir, ignore_errors=True)

        try:
            with closing(sqlite3.connect(self.server.database, timeout=15)) as db:
                event_jobs.initialize(db)
                with db:
                    db.execute(
                        """INSERT OR IGNORE INTO ci_jobs
                           (kind, sha, pr, trigger, source_delivery)
                           VALUES ('authoritative', ?, 0, ?, ?)""",
                        (submission_id, trigger, f"upload:{submission_id}"),
                    )
        except sqlite3.Error as error:
            logging.warning("Submission job enqueue failed: %s", error)
            self.respond_json(503, {"error": "queue_unavailable"})
            return

        self.respond_json(202, {
            "accepted": True,
            "submission_id": submission_id,
            "fast_track": fast,
        })

    def respond_json(self, status, payload):
        body = json.dumps(payload, separators=(",", ":")).encode("utf-8")
        self.close_connection = True
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(body)

    def respond(self, status):
        self.send_response(status)
        self.send_header("Content-Length", "0")
        self.end_headers()


def main():
    database = os.environ["GOLDBACH_WEBHOOK_DB"]
    with closing(sqlite3.connect(database)) as db, db:
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("""CREATE TABLE IF NOT EXISTS deliveries (
            id TEXT PRIMARY KEY, event TEXT NOT NULL, body BLOB NOT NULL,
            received_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        )""")
        event_jobs.initialize(db)
    secret = Path(os.environ["GOLDBACH_WEBHOOK_SECRET_FILE"]).read_bytes().strip()
    if len(secret) < 32:
        raise ValueError("Webhook secret is too short")
    desk_secret_file = os.environ.get("GOLDBACH_DESK_SECRET_FILE")
    desk_secret = Path(desk_secret_file).read_bytes().strip() if desk_secret_file else None
    if desk_secret is not None and len(desk_secret) < 32:
        raise ValueError("Desk secret is too short")
    submissions_dir = Path(os.environ.get(
        "GOLDBACH_SUBMISSIONS_DIR",
        str(Path(database).resolve().with_name("submissions")),
    ))
    with ThreadingHTTPServer(("127.0.0.1", 18081), Receiver) as server:
        server.secret = secret
        server.desk_secret = desk_secret
        server.submissions_dir = submissions_dir
        server.database = database
        server.serve_forever()


if __name__ == "__main__":
    main()
