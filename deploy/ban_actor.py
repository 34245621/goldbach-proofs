#!/usr/bin/env python3
"""Ban, unban, or inspect contributor accounts by immutable GitHub UID or handle."""

import argparse
import json
import os
import sqlite3
import time
from contextlib import closing
from pathlib import Path

from desk import canonical_handle


def open_moderation(state_dir):
    db_path = Path(state_dir) / "actor-moderation.sqlite3"
    conn = sqlite3.connect(db_path, timeout=15)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS actor_identities (
            github_uid INTEGER PRIMARY KEY,
            handle TEXT NOT NULL,
            updated_at INTEGER NOT NULL
        );
        CREATE INDEX IF NOT EXISTS actor_identities_handle ON actor_identities(handle);
        CREATE TABLE IF NOT EXISTS actor_bans (
            actor_key TEXT PRIMARY KEY,
            github_uid INTEGER,
            handle TEXT,
            reason TEXT NOT NULL,
            created_at INTEGER NOT NULL,
            expires_at INTEGER
        );
        CREATE TABLE IF NOT EXISTS actor_strikes (
            actor_key TEXT PRIMARY KEY,
            github_uid INTEGER,
            handle TEXT NOT NULL,
            strikes INTEGER NOT NULL DEFAULT 0,
            last_strike_at INTEGER NOT NULL,
            decayed_at INTEGER NOT NULL
        );
    """)
    return conn


def revoke_open_leases(state_dir, uid, handle, now):
    revoked = 0
    for db_file in Path(state_dir).glob("*.sqlite3"):
        if db_file.name in {"actor-moderation.sqlite3", "contributor-links.sqlite3", "page-views.sqlite3"}:
            continue
        with closing(sqlite3.connect(db_file, timeout=15)) as conn, conn:
            cols = {r[1] for r in conn.execute("PRAGMA table_info(goldbach_leases)")}
            if not cols:
                continue
            if uid and "github_uid" in cols:
                revoked += conn.execute("""
                    UPDATE goldbach_leases SET released_at = ?, release_reason = 'abandoned'
                    WHERE (github_uid = ? OR (? IS NOT NULL AND handle = ?))
                      AND run_id IS NULL AND released_at IS NULL AND finished_at IS NULL
                """, (now, uid, handle, handle)).rowcount
            elif handle:
                revoked += conn.execute("""
                    UPDATE goldbach_leases SET released_at = ?, release_reason = 'abandoned'
                    WHERE handle = ? AND run_id IS NULL AND released_at IS NULL AND finished_at IS NULL
                """, (now, handle)).rowcount
    return revoked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state-dir", default=os.environ.get("STATE_DIRECTORY", "/var/lib/goldbach-web"))
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--ban", action="store_true", help="ban an account by --uid and/or --handle")
    group.add_argument("--unban", action="store_true", help="lift bans and clear strikes for an account")
    group.add_argument("--list", action="store_true", help="list active bans and strike records")
    parser.add_argument("--uid", type=int, help="GitHub numeric user ID")
    parser.add_argument("--handle", help="GitHub login handle")
    parser.add_argument("--hours", type=float, help="temporary ban duration in hours (omit for permanent ban)")
    parser.add_argument("--reason", default="manual_moderation", help="ban reason label")
    args = parser.parse_args()

    now = int(time.time())
    handle = canonical_handle(args.handle) if args.handle else None
    if args.handle and not handle:
        parser.error("invalid GitHub handle")
    if args.uid is not None and args.uid < 1:
        parser.error("--uid must be a positive integer")

    with closing(open_moderation(args.state_dir)) as conn:
        if args.list:
            bans = [dict(r) for r in conn.execute(
                "SELECT * FROM actor_bans WHERE expires_at IS NULL OR expires_at > ? ORDER BY created_at DESC", (now,)
            )]
            strikes = [dict(r) for r in conn.execute("SELECT * FROM actor_strikes WHERE strikes > 0 ORDER BY strikes DESC")]
            print(json.dumps({"active_bans": bans, "strikes": strikes}, ensure_ascii=False, indent=2))
            return

        uid = args.uid
        if uid is None and handle:
            row = conn.execute(
                "SELECT github_uid FROM actor_identities WHERE handle = ? ORDER BY updated_at DESC LIMIT 1", (handle,)
            ).fetchone()
            if row:
                uid = row["github_uid"]
        if handle is None and uid is not None:
            row = conn.execute("SELECT handle FROM actor_identities WHERE github_uid = ?", (uid,)).fetchone()
            if row:
                handle = row["handle"]
        if uid is None and handle is None:
            parser.error("specify --uid and/or --handle")

        keys = []
        if uid is not None:
            keys.append(f"uid:{uid}")
        if handle is not None:
            keys.append(f"handle:{handle}")

        with conn:
            if args.ban:
                expires = None if args.hours is None else int(now + args.hours * 3600)
                for key in keys:
                    conn.execute(
                        "INSERT OR REPLACE INTO actor_bans VALUES (?, ?, ?, ?, ?, ?)",
                        (key, uid, handle, args.reason, now, expires),
                    )
                revoked = revoke_open_leases(args.state_dir, uid, handle, now)
                print(json.dumps({
                    "banned": True, "github_uid": uid, "handle": handle,
                    "permanent": expires is None, "expires_at": expires,
                    "reason": args.reason, "revoked_leases": revoked,
                }, ensure_ascii=False))
            else:
                removed = 0
                for key in keys:
                    removed += conn.execute("DELETE FROM actor_bans WHERE actor_key = ?", (key,)).rowcount
                    conn.execute("DELETE FROM actor_strikes WHERE actor_key = ?", (key,))
                if uid is not None:
                    removed += conn.execute("DELETE FROM actor_bans WHERE github_uid = ?", (uid,)).rowcount
                    conn.execute("DELETE FROM actor_strikes WHERE github_uid = ?", (uid,))
                if handle is not None:
                    removed += conn.execute("DELETE FROM actor_bans WHERE handle = ?", (handle,)).rowcount
                    conn.execute("DELETE FROM actor_strikes WHERE handle = ?", (handle,))
                print(json.dumps({"unbanned": True, "github_uid": uid, "handle": handle, "removed": removed}))


if __name__ == "__main__":
    main()
