"""Run a fixed-repository website, catalogue, GRH or proof check per Unix socket request."""

import json
import logging
import os
import re
import socketserver
import sqlite3
import subprocess
import tempfile
from contextlib import closing, contextmanager
from pathlib import Path
from threading import BoundedSemaphore, Event, Lock, Thread

from assemble import poll as poll_assemblies

from desk_outbox import clear_active_job, mark_active_job
from formal_proof import judge
from github_app import GitHubApp
from prepare_proof import ProofRefused, grh_enabled, prepare
from verify_proof import KProofWorker, ProofCancelled

ROOT = Path("/opt/goldbach-ci")
TRUSTED_BASE = Path(os.environ.get("GOLDBACH_TRUSTED_BASE", ROOT / "lean-replay"))
SOCKET = Path("/run/goldbach-ci-site/runner.sock")
MAX_PARALLEL_CHECKS = 12
MAX_SLOW_FORMAL_CHECKS = 8
MAX_THROTTLED_FORMAL_CHECKS = 2
HEARTBEAT_SECONDS = 15.0
PROOF_GITHUB = GitHubApp("/etc/goldbach-ci/github-app.pem", request_interval=0.25)
SLOW_FORMAL_SLOTS = BoundedSemaphore(MAX_SLOW_FORMAL_CHECKS)
THROTTLED_FORMAL_SLOTS = BoundedSemaphore(MAX_THROTTLED_FORMAL_CHECKS)
KPROOF_WORKER = KProofWorker(Path(os.environ.get("GOLDBACH_KPROOF_STAGE_DIR", "/run/goldbach-ci-site/kproof-stage")))


class ActiveProofRegistry:
    """Track in-flight proof containers per PR and stop superseded revisions."""

    def __init__(self):
        self._lock = Lock()
        self._runs = {}

    def supersede(self, pr, current_head):
        if pr <= 0:
            return
        stale = []
        with self._lock:
            for entry in self._runs.values():
                if entry["pr"] == pr and entry["head"] != current_head:
                    entry["cancelled"].set()
                    stale.extend(entry["containers"])
        for name in stale:
            subprocess.run(["docker", "rm", "-f", name],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)

    @contextmanager
    def track(self, pr, head):
        token = object()
        cancelled = Event()
        entry = {"pr": pr, "head": head, "cancelled": cancelled, "containers": set()}
        with self._lock:
            self._runs[token] = entry

        def on_container(name, started):
            kill_now = False
            with self._lock:
                if started:
                    if cancelled.is_set():
                        kill_now = True
                    else:
                        entry["containers"].add(name)
                else:
                    entry["containers"].discard(name)
            if kill_now:
                subprocess.run(["docker", "rm", "-f", name],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)

        try:
            yield on_container, cancelled
        finally:
            with self._lock:
                self._runs.pop(token, None)


ACTIVE_PROOFS = ActiveProofRegistry()


def run_with_keepalive(wfile, keepalive, action, *, on_tick=None, interval=HEARTBEAT_SECONDS):
    if not keepalive and on_tick is None:
        result = action()
        try:
            wfile.write(f"{result}\n".encode())
        except OSError:
            pass
        return result

    done = Event()
    outcome = [3]

    def worker():
        try:
            outcome[0] = action()
        except BaseException:
            logging.exception("Unhandled site runner worker exception")
            outcome[0] = 3
        finally:
            done.set()

    thread = Thread(target=worker, daemon=True)
    thread.start()
    while not done.wait(interval):
        if on_tick is not None:
            try:
                on_tick()
            except Exception:
                logging.warning("Could not refresh active job heartbeat", exc_info=True)
        if keepalive:
            try:
                wfile.write(b"running\n")
                wfile.flush()
            except OSError:
                keepalive = False
    thread.join()
    try:
        wfile.write(f"{outcome[0]}\n".encode())
        wfile.flush()
    except OSError:
        pass
    return outcome[0]


class RunnerServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    request_queue_size = 16
    daemon_threads = True

    def __init__(self, address, handler):
        self.slots = BoundedSemaphore(MAX_PARALLEL_CHECKS)
        super().__init__(address, handler)

    def process_request(self, request, client_address):
        self.slots.acquire()
        try:
            super().process_request(request, client_address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.slots.release()


class Handler(socketserver.StreamRequestHandler):
    def handle(self):
        self.connection.settimeout(15)
        line = self.rfile.readline(128)
        formal = re.fullmatch(rb"formal ([1-9][0-9]{0,17})( keepalive)?\n", line)
        if formal:
            job_id = int(formal[1])
            database = os.environ.get("GOLDBACH_CI_DATABASE")

            def refresh_heartbeat():
                if database:
                    with closing(sqlite3.connect(database, timeout=15)) as db:
                        mark_active_job(db, job_id)

            run_with_keepalive(self.wfile, bool(formal[2]), lambda: check_formal(job_id),
                               on_tick=refresh_heartbeat if database else None)
            return
        proof = re.fullmatch(rb"proof ([1-9][0-9]{0,9}) ([a-f0-9]{40})( keepalive)?\n", line)
        if proof:
            pr_number, head = int(proof[1]), proof[2].decode()
            run_with_keepalive(self.wfile, bool(proof[3]), lambda: check_proof(pr_number, head))
            return
        request = re.fullmatch(rb"(catalogue |grh )?([a-f0-9]{40})\n", line)
        if request is None:
            self.wfile.write(b"2\n")
            return
        if request[1] == b"grh " and not grh_enabled():
            self.wfile.write(b"3\nGRH verification is temporarily disabled\n")
            return
        sha = request[2].decode()
        diagnostics = b""
        try:
            with tempfile.TemporaryDirectory(prefix="goldbach-site-") as temporary:
                stage = Path(temporary)
                stage.chmod(0o755)
                subprocess.run([
                    "bash", str(ROOT / "controller/prepare-site-revision.sh"), sha, str(stage),
                    str(ROOT / "site-replay/check-site.sh"),
                ], check=True, timeout=120)
                if request[1] == b"grh ":
                    command = [ROOT / "controller/run-grh-revision.sh", stage / "source.tar"]
                elif request[1]:
                    command = [ROOT / "controller/run-catalogue-revision.sh", stage / "source.tar"]
                else:
                    command = [ROOT / "replay-site.sh", stage]
                if request[1] == b"grh ":
                    completed = subprocess.run([
                        "bash", "-o", "pipefail", "-c", 'bash "$@" 2>&1 | tail -c 32768',
                        "goldbach-grh", *command,
                    ], stdout=subprocess.PIPE, timeout=1850)
                    result = completed.returncode
                    diagnostics = completed.stdout
                else:
                    result = subprocess.run(["bash", *command], timeout=1850).returncode
        except (OSError, subprocess.SubprocessError):
            result = 3
        self.wfile.write(f"{result}\n".encode() + diagnostics)


def check_proof(number, head):
    try:
        base = TRUSTED_BASE.resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix="goldbach-proof-") as temporary:
            work = Path(temporary)
            prepare(PROOF_GITHUB, number, head, base, work)
        ACTIVE_PROOFS.supersede(number, head)
    except ProofRefused as error:
        logging.info("Advisory file guard refused PR %s at %s: %s", number, head, error)
        return 1
    except (ValueError, OSError, subprocess.SubprocessError):
        logging.exception("Proof check failed for PR %s at %s", number, head)
        return 3
    return 0


def check_formal(job_id):
    database = os.environ.get("GOLDBACH_CI_DATABASE")
    desk_url = os.environ.get("GOLDBACH_DESK_URL")
    secret_file = os.environ.get("GOLDBACH_DESK_SECRET_FILE")
    if not all((database, desk_url, secret_file)):
        logging.error("Formal proof runner configuration is missing")
        return 3
    try:
        base = TRUSTED_BASE.resolve(strict=True)
        with closing(sqlite3.connect(database, timeout=15)) as db, tempfile.TemporaryDirectory(
                prefix="goldbach-formal-") as temporary:
            mark_active_job(db, job_id)
            try:
                job_row = db.execute(
                    "SELECT pr, sha FROM ci_jobs WHERE id=? AND kind='authoritative'", (job_id,),
                ).fetchone()
                pr_number, head = job_row if job_row is not None else (0, "")
                submissions_dir = os.environ.get(
                    "GOLDBACH_SUBMISSIONS_DIR",
                    str(Path(database).resolve().with_name("submissions")),
                )
                with ACTIVE_PROOFS.track(pr_number, head) as (on_container, cancelled):
                    run = judge(
                        db, PROOF_GITHUB, job_id, Path(temporary), base,
                        ROOT / "toolchains/lean-4.36.0", ROOT / "controller/build-ownership.sh",
                        desk_url=desk_url, secret=Path(secret_file).read_bytes().strip(),
                        on_revision=ACTIVE_PROOFS.supersede,
                        on_container=on_container, cancelled=cancelled,
                        submissions_dir=submissions_dir,
                        kproof_worker=KPROOF_WORKER,
                        slow_slots=SLOW_FORMAL_SLOTS,
                        throttled_slots=THROTTLED_FORMAL_SLOTS,
                    )
                row = db.execute("SELECT payload FROM desk_outbox WHERE run=? AND attempt=1", (run,)).fetchone()
                return {"ACCEPTED": 0, "REJECTED": 1, "ERROR": 3}[json.loads(row[0])["verdict"]]
            finally:
                clear_active_job(db, job_id)
    except ProofRefused as error:
        logging.warning("Formal submission refused for job %s: %s", job_id, error)
        return 1
    except ProofCancelled as error:
        logging.info("Cancelled superseded formal proof check for job %s: %s", job_id, error)
        return 3
    except (ValueError, OSError, sqlite3.Error, subprocess.SubprocessError):
        logging.exception("Formal proof infrastructure error for job %s", job_id)
        return 3


def main():
    with RunnerServer(str(SOCKET), Handler) as server:
        os.chown(SOCKET, 0, 1000)
        SOCKET.chmod(0o660)
        desk_url = os.environ.get("GOLDBACH_DESK_URL")
        secret_file = os.environ.get("GOLDBACH_DESK_SECRET_FILE")
        if desk_url and secret_file:
            Thread(target=poll_assemblies, daemon=True,
                   args=(server.slots, TRUSTED_BASE, ROOT, desk_url.rstrip("/"), secret_file)).start()
        server.serve_forever()


if __name__ == "__main__":
    main()
