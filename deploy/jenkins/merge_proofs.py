"""Merge registered, independently accepted one-file Lean proofs and publish their sources."""

import argparse
import base64
import hashlib
import json
import logging
import os
import re
import shutil
import sqlite3
import subprocess
import tarfile
import tempfile
import time
from contextlib import closing, contextmanager
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlencode
from urllib.request import urlopen

from desk_verdict import report_published
from github_app import APP_ID, GitHubApp, INSTALLATION_ID, RateLimited
from github_revision import REPO, SHA, pull_request
from proof_blob import proof_blob
from verdict_manifest import MODULE, PROOF_MODULE, module_path

CONTENTS_WRITE = {"contents": "write", "pull_requests": "read", "checks": "write"}
TRUST_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "CheckLemma.lean")
BATCH = 4
CATALOGUES = ("research/gaps.json", "research/problems.json")
DESK_HEALTH = "https://www.movan.tech/goldbach/health"
ROOT = Path("/opt/goldbach-ci")


class SkipMerge(ValueError):
    """The registered revision is no longer eligible."""


def task(base, gap_id):
    research = base / "research"
    gaps = json.loads((research / "gaps.json").read_bytes())["gaps"]
    for problem in json.loads((research / "problems.json").read_bytes()).values():
        gaps.extend(problem["gaps"])
    matches = [gap for gap in gaps if gap["id"] == gap_id]
    if len(matches) != 1 or not PROOF_MODULE.fullmatch(matches[0]["module"]):
        raise SkipMerge("No current registered community proof file")
    return matches[0]


def metadata(app, path, revision):
    if not SHA.fullmatch(revision):
        raise ValueError("Expected a full GitHub revision")
    data = app.request("GET", f"{REPO}/contents/{path}?ref={revision}")
    if not isinstance(data, dict) or data.get("type") != "file" or data.get("path") != path:
        raise ValueError("Expected a plain GitHub file")
    return data


def git_blob(content):
    return hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()


def revision_tree(app, revision):
    if not SHA.fullmatch(revision):
        raise ValueError("Expected a full GitHub revision")
    commit = app.request("GET", f"{REPO}/git/commits/{revision}")
    tree_sha = commit["tree"]["sha"]
    if commit["sha"] != revision or not SHA.fullmatch(tree_sha):
        raise ValueError("GitHub returned a different merge base")
    tree = app.request("GET", f"{REPO}/git/trees/{tree_sha}?recursive=1")
    if tree["sha"] != tree_sha or tree["truncated"]:
        raise ValueError("GitHub did not return the complete main tree")
    return {entry["path"]: entry for entry in tree["tree"]}


def verify_dependency(tree, base, path, expected=None):
    content = (base / path).read_bytes()
    if expected is not None and hashlib.sha256(content).hexdigest() != expected:
        raise ValueError(f"Verified dependency changed in the Jenkins baseline: {path}")
    entry = tree.get(path, {})
    if (entry.get("type") != "blob" or entry.get("mode") != "100644"
            or entry.get("sha") != git_blob(content)):
        raise ValueError(f"Verified dependency or pinned Lean input changed on main: {path}")


def manifest_hashes(record, target):
    manifest = record["manifest"]
    hashes = {}
    for item in manifest["rests_on"] + manifest["defs"]:
        module = item["module"]
        digest = item["sha256"]
        if (not MODULE.fullmatch(module) or not re.fullmatch(r"[0-9a-f]{64}", digest)
                or hashes.setdefault(module, digest) != digest):
            raise ValueError("Invalid proof dependency manifest")
    if target not in hashes:
        raise ValueError("The verified manifest does not include the target theorem")
    return hashes


def current_head(pr, expected):
    return (pr["head"]["sha"] == expected
            and pr["base"]["ref"] == "main"
            and pr["base"]["repo"]["full_name"] == REPO.removeprefix("/repos/"))


def proven_content(app, path, revision, expected):
    entry = metadata(app, path, revision)
    content = proof_blob(app, entry["sha"], entry["size"])
    if hashlib.sha256(content).hexdigest() != expected:
        raise SkipMerge("The GitHub proof bytes differ from the official verdict")
    return content


def resolve_record_target(record, base):
    module = record.get("module", "")
    generated = re.fullmatch(r"Conjectures\.Cuts\.(Task|Cut|Refute)[0-9a-f]{24}", module)
    kind = record.get("kind", "prove")
    if generated:
        if generated[1] != {"prove": "Task", "cut": "Cut", "refute": "Refute"}.get(kind):
            raise SkipMerge("The verified task kind differs from its assigned module")
        gap = {"module": module, "file": "lean/" + module_path(module)}
    else:
        if kind != "prove":
            raise SkipMerge("Missing assigned module in the verdict")
        gap = task(base, record["lemma_id"])
    path = gap["file"]
    module = path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
    if gap["module"] != module or path != "lean/" + module_path(module):
        raise SkipMerge("The task does not map to its registered module")
    return path, module


def publish_main_check(app, commit_sha, record):
    name = "Goldbach CI / formal Lean verdict"
    external_id = f"main:authoritative:{commit_sha}:{record['run_id']}"
    try:
        query = urlencode({"check_name": name, "app_id": APP_ID, "per_page": 50})
        found = app.request("GET", f"{REPO}/commits/{commit_sha}/check-runs?{query}")
        for item in found.get("check_runs", ()):
            if (item.get("external_id") == external_id
                    and item.get("head_sha") == commit_sha
                    and (item.get("app") or {}).get("id") == APP_ID):
                return item["id"]
        created = app.request("POST", f"{REPO}/check-runs", {
            "name": name,
            "head_sha": commit_sha,
            "external_id": external_id,
            "status": "completed",
            "conclusion": "success",
            "output": {
                "title": name,
                "summary": f"Lean verdict for {record['lemma_id']}: ACCEPTED. Task desk run {record['run_id']}.",
            },
        })
        return created.get("id")
    except (HTTPError, URLError, TimeoutError, KeyError, ValueError) as exc:
        logging.warning("Could not publish check-run on main commit %s: %s", commit_sha, exc)
        return None


def merge_private(app, submission_id, record, base, submissions_dir, *, dry_run=False):
    if record["verdict"] != "ACCEPTED" or record.get("head_sha") != submission_id:
        raise SkipMerge("No official ACCEPTED verdict for this submission")
    path, module = resolve_record_target(record, base)
    hashes = manifest_hashes(record, module)
    expected_sha256 = hashes.pop(module)

    main_sha = app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"]
    tree = revision_tree(app, main_sha)
    if path in tree:
        existing_entry = tree[path]
        if existing_entry.get("type") == "blob" and existing_entry.get("mode") == "100644":
            existing_bytes = proof_blob(app, existing_entry["sha"], existing_entry["size"])
            if hashlib.sha256(existing_bytes).hexdigest() == expected_sha256:
                commits = app.request("GET", f"{REPO}/commits?sha={main_sha}&path={path}&per_page=1")
                commit_sha = commits[0]["sha"] if isinstance(commits, list) and commits else main_sha
                return commit_sha, path, existing_bytes
        raise SkipMerge("The registered proof path already exists on main")

    if submissions_dir is None:
        raise ValueError("Missing submissions directory for private proof publication")
    bundle_dir = Path(submissions_dir) / submission_id
    source_file = bundle_dir / "proof.lean"
    ticket_file = bundle_dir / "ticket.json"
    if not source_file.is_file() or source_file.is_symlink() or not ticket_file.is_file():
        raise SkipMerge("Private proof bundle is no longer present on disk")
    content = source_file.read_bytes()
    if hashlib.sha256(content).hexdigest() != expected_sha256:
        raise SkipMerge("Private proof bytes on disk differ from the official verdict")
    ticket = json.loads(ticket_file.read_text(encoding="utf-8"))
    handle = ticket.get("handle", "contributor")
    uid = ticket.get("github_uid")

    for name in TRUST_FILES:
        verify_dependency(tree, base, "lean/" + name)
    for name, digest in hashes.items():
        verify_dependency(tree, base, "lean/" + module_path(name), digest)
    if dry_run:
        return None, path, content

    blob = app.request("POST", f"{REPO}/git/blobs", {
        "content": base64.b64encode(content).decode("ascii"),
        "encoding": "base64",
    })
    if blob.get("sha") != git_blob(content):
        raise ValueError("GitHub returned an unexpected blob SHA for verified proof")

    email = f"{uid}+{handle}@users.noreply.github.com" if uid else f"{handle}@users.noreply.github.com"
    message = (
        f"Verify {record['lemma_id']} ({module})\n\n"
        f"Task desk run: {record['run_id']}\n"
        f"Contributor: @{handle}"
    )

    committed_sha = None
    for attempt in range(3):
        if attempt > 0:
            main_sha = app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"]
            tree = revision_tree(app, main_sha)
            if path in tree:
                raise SkipMerge("The registered proof path already exists on main")
            for name in TRUST_FILES:
                verify_dependency(tree, base, "lean/" + name)
            for name, digest in hashes.items():
                verify_dependency(tree, base, "lean/" + module_path(name), digest)
        base_commit = app.request("GET", f"{REPO}/git/commits/{main_sha}")
        new_tree = app.request("POST", f"{REPO}/git/trees", {
            "base_tree": base_commit["tree"]["sha"],
            "tree": [{
                "path": path,
                "mode": "100644",
                "type": "blob",
                "sha": blob["sha"],
            }],
        })
        commit = app.request("POST", f"{REPO}/git/commits", {
            "message": message,
            "tree": new_tree["sha"],
            "parents": [main_sha],
            "author": {"name": handle, "email": email},
        })
        try:
            app.request("PATCH", f"{REPO}/git/refs/heads/main", {
                "sha": commit["sha"],
                "force": False,
            })
            committed_sha = commit["sha"]
            break
        except HTTPError as exc:
            if exc.code == 422 and attempt < 2:
                continue
            raise
    if not committed_sha or not SHA.fullmatch(committed_sha):
        raise ValueError("Failed to advance main with verified proof commit")
    if metadata(app, path, committed_sha)["sha"] != git_blob(content):
        raise ValueError("GitHub commit on main did not preserve the verified source")
    return committed_sha, path, content


def merge(app, number, head, record, base, *, dry_run=False):
    if record["verdict"] != "ACCEPTED" or record["head_sha"] != head:
        raise SkipMerge("No official ACCEPTED verdict for this revision")
    path, module = resolve_record_target(record, base)
    hashes = manifest_hashes(record, module)
    pr = pull_request(app, number)
    if not current_head(pr, head):
        raise SkipMerge("The pull request head or target has changed")

    if pr["merged"]:
        commit = pr["merge_commit_sha"]
        content = proven_content(app, path, commit, hashes[module])
        # A manually merged proof may have been reverted. Import only sources still on main.
        main = app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"]
        if metadata(app, path, main)["sha"] != git_blob(content):
            raise SkipMerge("The merged proof differs from main")
        return commit, path, content
    if pr["state"] != "open":
        raise SkipMerge("The pull request was closed")
    if pr["draft"]:
        raise ValueError("The pull request is a draft")

    files = app.request("GET", f"{REPO}/pulls/{number}/files?per_page=2")
    if (pr["changed_files"] != 1 or len(files) != 1 or files[0]["filename"] != path
            or files[0]["status"] != "added"):
        raise SkipMerge("The pull request must add only the registered Lean file")
    # GitHub can keep the PR's base SHA at the historical branch point.
    base_revision = app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"]
    tree = revision_tree(app, base_revision)
    if path in tree:
        raise SkipMerge("The registered proof path already exists on main")
    if pr["mergeable"] is False:
        raise ValueError("The pull request has a merge conflict")
    content = proven_content(app, path, head, hashes.pop(module))
    for name in TRUST_FILES:
        verify_dependency(tree, base, "lean/" + name)
    for name, digest in hashes.items():
        verify_dependency(tree, base, "lean/" + module_path(name), digest)
    if dry_run:
        return None, path, content

    latest = pull_request(app, number)
    if not current_head(latest, head) or latest["state"] != "open" or latest["draft"]:
        raise ValueError("The pull request changed before its merge")
    if app.request("GET", f"{REPO}/git/ref/heads/main")["object"]["sha"] != base_revision:
        raise ValueError("main advanced while verifying the merge base")
    result = app.request("PUT", f"{REPO}/pulls/{number}/merge",
                         {"sha": head, "merge_method": "squash"})
    if not result.get("merged") or not SHA.fullmatch(result.get("sha", "")):
        raise ValueError("GitHub did not merge the exact verified revision")
    if metadata(app, path, result["sha"])["sha"] != git_blob(content):
        raise ValueError("GitHub merge did not preserve the verified source")
    return result["sha"], path, content


@contextmanager
def snapshot_for(store, base, revision):
    with tempfile.TemporaryDirectory(prefix="stage-", dir=store) as folder:
        snapshot = Path(folder) / "base"
        subprocess.run(["cp", "-al", base, snapshot], check=True, timeout=90)
        yield snapshot
        target = store / f"{revision}-{Path(folder).name}"
        snapshot.rename(target)
        link = Path(folder) / "current"
        link.symlink_to(target)
        os.replace(link, store / "current")


def publish_source(store, base, revision, path, content):
    previous = base / path
    module = path.removeprefix("lean/").removesuffix(".lean").replace("/", ".")
    if not PROOF_MODULE.fullmatch(module) or path != "lean/" + module_path(module):
        raise ValueError("Invalid verified module path")
    registry = base / "verified-imports.json"
    verified = json.loads(registry.read_bytes()) if registry.exists() else {}
    digest = hashlib.sha256(content).hexdigest()
    exists = previous.is_file() and not previous.is_symlink() and previous.read_bytes() == content
    if exists and verified.get(module) == digest:
        return
    if previous.exists() and not exists:
        raise ValueError("Refusing to overwrite an existing trusted proof")
    with snapshot_for(store, base, revision) as snapshot:
        if not exists:
            (snapshot / path).parent.mkdir(parents=True, exist_ok=True)
            (snapshot / path).write_bytes(content)
        verified[module] = digest
        index = snapshot / "verified-imports.json"
        index.unlink(missing_ok=True)
        index.write_text(json.dumps(verified, sort_keys=True, indent=2) + "\n", encoding="ascii")
        # The copied files are hard-linked. Replace any marker before writing.
        marker = snapshot / "PROOF_MERGE_REVISION"
        marker.unlink(missing_ok=True)
        marker.write_text(revision + "\n", encoding="ascii")


def sync_published_catalogue(app, store):
    with urlopen(DESK_HEALTH, timeout=10) as response:
        health = json.loads(response.read(4096))
    revision = health["catalogue_revision"]
    if health["status"] != "ok" or not SHA.fullmatch(revision or ""):
        raise ValueError("The task desk did not report a healthy catalogue revision")
    base = (store / "current").resolve(strict=True)
    marker = base / "CATALOGUE_REVISION"
    if marker.is_file() and marker.read_text().strip() == revision:
        return
    comparison = app.request("GET", f"{REPO}/compare/{revision}...main?per_page=1")
    if comparison["merge_base_commit"]["sha"] != revision:
        raise ValueError("The published catalogue is outside main history")
    checks = app.request("GET", f"{REPO}/commits/{revision}/check-runs?check_name=Goldbach+CI+%2F+catalogue+release")
    if not any(check["name"] == "Goldbach CI / catalogue release"
               and check["head_sha"] == revision and check["conclusion"] == "success"
               and check["app"]["id"] == APP_ID for check in checks["check_runs"]):
        raise ValueError("The published catalogue has no successful release check for its exact commit")
    with tempfile.TemporaryDirectory(prefix="catalogue-", dir=store) as folder:
        stage = Path(folder)
        subprocess.run(["bash", ROOT / "controller/prepare-site-revision.sh", revision, stage,
                        ROOT / "site-replay/check-site.sh"], check=True, timeout=120)
        with tarfile.open(stage / "source.tar") as archive, snapshot_for(store, base, revision) as snapshot:
            for name in TRUST_FILES:
                with archive.extractfile("lean/" + name) as upstream:
                    if upstream.read() != (base / "lean" / name).read_bytes():
                        raise ValueError(f"The published catalogue requires a new Lean baseline: {name}")
            for name in CATALOGUES:
                with archive.extractfile(name) as source:
                    document = source.read(20 * 1024 * 1024)
                json.loads(document)
                destination = snapshot / name
                destination.unlink()
                destination.write_bytes(document)
            marker = snapshot / "CATALOGUE_REVISION"
            marker.unlink(missing_ok=True)
            marker.write_text(revision + "\n", encoding="ascii")
    logging.info("Published Jenkins catalogue from %s", revision)


def eligible(db, first_job_id):
    return db.execute("""SELECT j.id,j.pr,j.sha,o.payload,coalesce(m.attempts,0)
        FROM ci_jobs j JOIN desk_runs r ON r.job_id=j.id
        JOIN desk_outbox o ON o.run=r.run_id AND o.attempt=1
        JOIN jenkins_dispatches d ON d.job_id=j.id AND d.result='SUCCESS'
        LEFT JOIN proof_merges m ON m.job_id=j.id
        WHERE j.kind='authoritative' AND j.pr>=0 AND j.id>=? AND o.delivered=1
          AND json_extract(o.payload,'$.verdict')='ACCEPTED'
          AND (m.job_id IS NULL OR (m.state='retry' AND m.retry_at<=?))
        ORDER BY j.id LIMIT ?""", (first_job_id, int(time.time()), BATCH)).fetchall()


def drain(db, app, store, first_job_id, *, dry_run=False, submissions_dir=None, desk_url=None, desk_secret=None):
    db.execute("""CREATE TABLE IF NOT EXISTS proof_merges (
        job_id INTEGER PRIMARY KEY, state TEXT NOT NULL, revision TEXT,
        attempts INTEGER NOT NULL, retry_at INTEGER NOT NULL)""")
    for job_id, pr, head, payload, attempts in eligible(db, first_job_id):
        revision, retry_at = None, 0
        record = json.loads(payload)
        try:
            base = (store / "current").resolve(strict=True)
            if pr == 0:
                revision, path, content = merge_private(
                    app, head, record, base, submissions_dir, dry_run=dry_run,
                )
                if dry_run:
                    print(f"Submission {head} verified for publish: {path}", flush=True)
                    continue
                publish_source(store, base, revision, path, content)
                check_id = publish_main_check(app, revision, record)
                if desk_url and desk_secret:
                    report_published(
                        desk_url,
                        desk_secret,
                        run_id=record["run_id"],
                        gap=record["lemma_id"],
                        commit_sha=revision,
                        check_id=check_id,
                    )
                if submissions_dir is not None:
                    shutil.rmtree(Path(submissions_dir) / head, ignore_errors=True)
                state = "merged"
                logging.info("Private submission %s proof source published at %s", head, revision)
            else:
                revision, path, content = merge(app, pr, head, record, base, dry_run=dry_run)
                if dry_run:
                    print(f"PR {pr} verified for merge: {path}", flush=True)
                    continue
                publish_source(store, base, revision, path, content)
                state = "merged"
                logging.info("PR %s proof source published from %s", pr, revision)
        except RateLimited:
            logging.info("GitHub requested a cooldown")
            break
        except SkipMerge as error:
            state = "skipped"
            if pr == 0 and submissions_dir is not None and not dry_run:
                shutil.rmtree(Path(submissions_dir) / head, ignore_errors=True)
            logging.info("Submission %s: %s", pr or head, error)
        except (HTTPError, URLError, TimeoutError, OSError, ValueError, subprocess.SubprocessError) as error:
            state = "retry"
            retry_at = int(time.time()) + min(3600, 60 * 2 ** min(6, attempts))
            reason = f"HTTP {error.code}" if isinstance(error, HTTPError) else str(error)
            logging.warning("Submission %s: %s", pr or head, reason)
        if not dry_run:
            with db:
                db.execute("""INSERT OR REPLACE INTO proof_merges VALUES (?,?,?,?,?)""",
                           (job_id, state, revision, attempts + 1, retry_at))


SNAPSHOT_NAME = re.compile(r"^[0-9a-f]{40}-stage-[A-Za-z0-9_-]+$")


def prune_snapshots(store, *, keep_recent=32, min_age_seconds=3 * 3600, max_delete=25, now=None):
    current_link = store / "current"
    if not current_link.exists():
        return 0
    active = current_link.resolve(strict=True)
    timestamp = time.time() if now is None else now
    snapshots = []
    for entry in store.iterdir():
        if not SNAPSHOT_NAME.fullmatch(entry.name) or entry.is_symlink():
            continue
        try:
            stat = entry.stat()
            if not entry.is_dir() or entry.resolve() == active:
                continue
        except OSError:
            continue
        snapshots.append((stat.st_mtime, entry))
    snapshots.sort(key=lambda item: item[0], reverse=True)
    expired = [entry for mtime, entry in snapshots[keep_recent:] if timestamp - mtime >= min_age_seconds]
    removed = 0
    for entry in reversed(expired):
        if removed >= max_delete:
            break
        try:
            shutil.rmtree(entry)
            removed += 1
        except OSError as error:
            logging.warning("Could not remove old proof snapshot %s: %s", entry.name, error)
    if removed:
        logging.info("Pruned %s expired proof snapshots from %s", removed, store)
    return removed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", required=True, type=Path)
    parser.add_argument("--private-key", required=True)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--first-job-id", required=True, type=int)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    permissions = {"contents": "read", "pull_requests": "read"} if args.dry_run else CONTENTS_WRITE
    app = GitHubApp(args.private_key, permissions=permissions, request_interval=0.35)
    if not args.dry_run:
        installation = app.app_request("GET", f"/app/installations/{INSTALLATION_ID}")
        if installation["permissions"].get("contents") != "write":
            logging.info("Waiting for GitHub installation Contents write approval")
            return
        if installation["permissions"].get("checks") != "write":
            app = GitHubApp(args.private_key, permissions={
                "contents": "write", "pull_requests": "read",
            }, request_interval=0.35)
    submissions_dir = Path(os.environ.get(
        "GOLDBACH_SUBMISSIONS_DIR",
        str(args.database.resolve().with_name("submissions")),
    ))
    desk_url = os.environ.get("GOLDBACH_DESK_URL")
    desk_secret_file = os.environ.get("GOLDBACH_DESK_SECRET_FILE")
    desk_secret = Path(desk_secret_file).read_bytes().strip() if desk_secret_file else None
    with closing(sqlite3.connect(args.database.resolve().as_uri() + "?mode=rw", uri=True, timeout=15)) as db:
        store = args.store.resolve(strict=True)
        if not args.dry_run:
            try:
                sync_published_catalogue(app, store)
            except (OSError, ValueError, KeyError, RateLimited, subprocess.SubprocessError) as error:
                logging.warning("Catalogue sync deferred: %s", error)
        drain(
            db, app, store, args.first_job_id, dry_run=args.dry_run,
            submissions_dir=submissions_dir, desk_url=desk_url, desk_secret=desk_secret,
        )
        if not args.dry_run:
            prune_snapshots(store)
            from register_proof_imports import open_import_pr, pending_imports
            try:
                if pending_imports((store / "current").resolve(strict=True)):
                    if installation["permissions"].get("pull_requests") != "write":
                        logging.warning("Automatic import registration requires GitHub App Pull requests write")
                        return
                    registrar = GitHubApp(args.private_key, permissions={
                        "contents": "write", "pull_requests": "write"
                    }, request_interval=0.35)
                    open_import_pr(registrar, store, ROOT, REPO, revision_tree, git_blob)
            except (OSError, ValueError, KeyError, RateLimited, subprocess.SubprocessError) as error:
                logging.warning("Automatic import registration deferred: %s", error)


if __name__ == "__main__":
    main()
