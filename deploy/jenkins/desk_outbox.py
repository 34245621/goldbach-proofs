"""Store signed desk verdict inputs independently of proof execution."""

import argparse
import json
import sqlite3
import time
from contextlib import closing
from pathlib import Path
from urllib.error import HTTPError, URLError

from desk_verdict import send_verdict, signed_post
from event_jobs import desk_run_id


ACTIVE_HEARTBEAT_TTL = 120


def initialize(db):
    db.execute("""CREATE TABLE IF NOT EXISTS desk_outbox (
        run INTEGER NOT NULL, attempt INTEGER NOT NULL, payload BLOB NOT NULL,
        retries INTEGER NOT NULL DEFAULT 0, retry_at INTEGER NOT NULL DEFAULT 0,
        delivered INTEGER NOT NULL DEFAULT 0, error TEXT,
        PRIMARY KEY (run, attempt)
    )""")


def mark_active_job(db, job_id, *, now=None):
    timestamp = int(time.time() if now is None else now)
    with db:
        db.execute("""CREATE TABLE IF NOT EXISTS active_formal_jobs (
            job_id INTEGER PRIMARY KEY, heartbeat_at INTEGER NOT NULL
        )""")
        db.execute("DELETE FROM active_formal_jobs WHERE heartbeat_at <= ?",
                   (timestamp - ACTIVE_HEARTBEAT_TTL * 10,))
        db.execute("INSERT OR REPLACE INTO active_formal_jobs (job_id, heartbeat_at) VALUES (?, ?)",
                   (job_id, timestamp))


def clear_active_job(db, job_id):
    with db:
        if db.execute(
            "SELECT 1 FROM sqlite_master WHERE type='table' AND name='active_formal_jobs'"
        ).fetchone():
            db.execute("DELETE FROM active_formal_jobs WHERE job_id=?", (job_id,))


def enqueue(db, record):
    run, attempt = record["run_id"], record["run_attempt"]
    if (type(run) is not int or run < 1 or type(attempt) is not int or attempt < 1
            or record["verdict"] not in ("ACCEPTED", "REJECTED")):
        raise ValueError("Invalid desk verdict identity or conclusion")
    payload = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
    if len(payload) > 262144:
        raise ValueError("Desk verdict exceeds the API limit")
    with db:
        db.execute("INSERT OR IGNORE INTO desk_outbox (run, attempt, payload) VALUES (?, ?, ?)",
                   (run, attempt, payload))
        previous = db.execute("SELECT payload FROM desk_outbox WHERE run=? AND attempt=?",
                              (run, attempt)).fetchone()
        if previous[0] != payload:
            raise ValueError("The run attempt already has a different verdict")


def enqueue_runner_failures(db, since, *, now=None):
    """Reconcile finished Jenkins runs that never produced a Lean verdict."""
    tables = {row[0] for row in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
    if not {"ci_jobs", "desk_runs", "jenkins_dispatches"} <= tables:
        return
    have_refusals = "proof_refusals" in tables
    refused = ("AND NOT EXISTS (SELECT 1 FROM proof_refusals f WHERE f.job_id=j.id)"
               if have_refusals else "")
    have_active = "active_formal_jobs" in tables
    cutoff = int(time.time() if now is None else now) - ACTIVE_HEARTBEAT_TTL
    not_active = ("AND NOT EXISTS (SELECT 1 FROM active_formal_jobs a WHERE a.job_id=j.id AND a.heartbeat_at>?)"
                  if have_active else "")
    not_revision_active = (
        """AND NOT EXISTS (
              SELECT 1 FROM ci_jobs j3 JOIN active_formal_jobs a3 ON a3.job_id=j3.id
              WHERE j3.kind='authoritative' AND j3.pr=j.pr AND j3.sha=j.sha AND a3.heartbeat_at>?
          )""" if have_active else ""
    )
    max_before = db.execute(
        "SELECT coalesce(max(job_id), 0) + 1 FROM desk_runs WHERE run_id<?", (since,)
    ).fetchone()[0]
    min_after = db.execute(
        "SELECT min(job_id) FROM desk_runs WHERE run_id>=?", (since,)
    ).fetchone()[0]
    min_job_id = max_before if min_after is None else min(max_before, min_after)
    unstarted_params = (min_job_id, cutoff, cutoff) if have_active else (min_job_id,)
    unstarted = db.execute(f"""
        SELECT j.id, j.pr, j.sha FROM ci_jobs j
        JOIN jenkins_dispatches d ON d.job_id=j.id
        WHERE j.kind='authoritative' AND j.pr>0 AND j.id>=?
          AND d.result IN ('FAILURE', 'ABORTED', 'CANCELLED', 'UNSTABLE', 'NOT_BUILT')
          AND NOT EXISTS (SELECT 1 FROM desk_runs r WHERE r.job_id=j.id)
          AND NOT EXISTS (
              SELECT 1 FROM ci_jobs j2 JOIN desk_runs r2 ON r2.job_id=j2.id
              WHERE j2.kind='authoritative' AND j2.pr=j.pr AND j2.sha=j.sha
          )
          {refused}
          {not_active}
          {not_revision_active}
        ORDER BY j.id DESC
    """, unstarted_params).fetchall()
    seen_revisions = set()
    for job_id, pr, sha in unstarted:
        if (pr, sha) in seen_revisions:
            continue
        seen_revisions.add((pr, sha))
        desk_run_id(db, job_id)
    row_params = (since, cutoff) if have_active else (since,)
    rows = db.execute(f"""
        SELECT j.pr, j.sha, r.run_id FROM ci_jobs j
        JOIN desk_runs r ON r.job_id=j.id
        JOIN jenkins_dispatches d ON d.job_id=j.id
        WHERE j.kind='authoritative' AND j.pr>0 AND r.run_id>=?
          AND d.result IN ('FAILURE', 'ABORTED', 'CANCELLED', 'UNSTABLE', 'NOT_BUILT')
          AND NOT EXISTS (SELECT 1 FROM desk_outbox o WHERE o.run=r.run_id AND o.attempt=1)
          {refused}
          {not_active}
    """, row_params).fetchall()
    with db:
        for pr, sha, run in rows:
            payload = json.dumps({"pr": pr, "head_sha": sha, "run_id": run, "run_attempt": 1,
                                  "verdict": "ERROR"}, sort_keys=True, separators=(",", ":")).encode()
            db.execute("INSERT OR IGNORE INTO desk_outbox (run, attempt, payload) VALUES (?, 1, ?)",
                       (run, payload))


def drain(db, url, secret):
    now = int(time.time())
    rows = db.execute("""SELECT run,attempt,payload,retries FROM desk_outbox
                         WHERE delivered=0 AND retry_at<=? ORDER BY run,attempt LIMIT 20""", (now,))
    for run, attempt, payload, retries in rows.fetchall():
        try:
            if json.loads(payload)["verdict"] == "ERROR":
                failure_url = url.removesuffix("/api/verdict") + "/api/desk/check-failed"
                signed_post(failure_url, secret, payload, {"status": "stored"})
            else:
                send_verdict(url, secret, payload)
        except HTTPError as error:
            retry_after = error.headers.get("Retry-After", "")
            delay = min(3600, 30 * 2 ** min(retries, 7))
            if retry_after.isdecimal():
                delay = max(delay, int(retry_after))
            message = f"HTTP {error.code}"
        except (URLError, TimeoutError, RuntimeError, json.JSONDecodeError) as error:
            delay = min(3600, 30 * 2 ** min(retries, 7))
            message = type(error).__name__
        else:
            with db:
                db.execute("UPDATE desk_outbox SET delivered=1,error=NULL WHERE run=? AND attempt=?",
                           (run, attempt))
            continue
        with db:
            db.execute("""UPDATE desk_outbox SET retries=retries+1,retry_at=?,error=?
                          WHERE run=? AND attempt=?""", (int(time.time()) + delay, message, run, attempt))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=Path)
    parser.add_argument("--verdict-url", required=True)
    parser.add_argument("--secret-file", required=True, type=Path)
    args = parser.parse_args()
    with closing(sqlite3.connect(args.database.resolve().as_uri() + "?mode=rw", uri=True, timeout=15)) as db:
        initialize(db)
        enqueue_runner_failures(db, int(time.time() - 3 * 3600) * 1_000_000)
        drain(db, args.verdict_url, args.secret_file.read_bytes().strip())


if __name__ == "__main__":
    main()
