"""Authorize a formal proof and durably record the kernel result."""

import json
import logging
import os
import re
import shutil
from contextlib import nullcontext
from pathlib import Path

from desk_outbox import enqueue, initialize
from desk_verdict import (
    DeskRefused,
    authorize,
    precheck,
    report_diagnostic,
    report_kernel_verified,
    report_moderation,
)
from event_jobs import desk_run_id
from github_revision import REPO, StaleDelivery, pull_request
from prepare_proof import ProofRefused, prepare, prepare_bundle
from verify_proof import ProofRejected, classify_kproof_rejection, verify

COMMENT_COMMAND = re.compile(r"/goldbach-check (L-[a-z0-9]+(?:-[a-z0-9]+)*)")
BUNDLE_TRIGGER = re.compile(r"bundle:(?:fast|slow):([0-9a-f]{40})")
BYPASSED_GUARD_PATTERNS = (
    re.compile(r'^line \d+: ".*" is not allowed in a proof file\b'),
    re.compile(r'^line \d+: the word "import" after the import lines\b'),
    re.compile(r"^the file holds (?:control|invisible|no theorem|a NUL byte)\b"),
    re.compile(r"^the file is not UTF-8 text\b"),
)


def is_bypassed_local_guard(reason):
    text = str(reason or "").strip()
    return any(pattern.search(text) for pattern in BYPASSED_GUARD_PATTERNS)


def _safe_desk_call(fn, *args, **kwargs):
    try:
        return fn(*args, **kwargs)
    except Exception:
        logging.warning("Auxiliary Desk callback failed", exc_info=True)
        return None


def record_refusal(db, job_id, reason):
    with db:
        db.execute("""CREATE TABLE IF NOT EXISTS proof_refusals (
            job_id INTEGER PRIMARY KEY, reason TEXT NOT NULL
        )""")
        db.execute("INSERT OR IGNORE INTO proof_refusals VALUES (?, ?)", (job_id, str(reason)))


def _judge_bundle(db, job_id, run_id, head, work, base, toolchain, ownership_check, *,
                  desk_url, secret, submissions_dir, kproof_worker, slow_slots,
                  on_container, cancelled):
    bundle_dir = Path(submissions_dir) / head
    if not bundle_dir.is_dir():
        raise ValueError(f"Missing private submission bundle directory for {head}")
    ticket = json.loads((bundle_dir / "ticket.json").read_text(encoding="utf-8"))
    handle = ticket["handle"]
    github_uid = ticket.get("github_uid")
    gap_hint = ticket["gap"]

    if desk_url:
        try:
            precheck(desk_url, secret, pr=0, head=head, handle=handle, gap=gap_hint, run_id=run_id)
        except DeskRefused as error:
            reason = f"Task desk refused authorization: {error}"
            record_refusal(db, job_id, reason)
            _safe_desk_call(report_diagnostic, desk_url, secret, gap=gap_hint, head=head, diagnostic=reason)
            shutil.rmtree(bundle_dir, ignore_errors=True)
            raise ProofRefused(reason) from None

    try:
        file = prepare_bundle(bundle_dir, base, work)
    except ProofRefused as error:
        reason = str(error)
        record_refusal(db, job_id, reason)
        if desk_url:
            if is_bypassed_local_guard(reason):
                _safe_desk_call(
                    report_moderation, desk_url, secret,
                    kind="tamper", handle=handle, github_uid=github_uid,
                    gap=gap_hint, head=head, detail=f"Guard violation in private bundle: {reason}",
                )
            else:
                _safe_desk_call(
                    report_diagnostic, desk_url, secret,
                    gap=gap_hint, head=head, diagnostic=f"REFUSED: {reason}",
                )
        shutil.rmtree(bundle_dir, ignore_errors=True)
        raise

    gap = (work / "gap.id").read_text().strip()
    statement = (work / "statement.txt").read_bytes()
    kind = (work / "task.kind").read_text().strip()
    module = (work / "pr.module").read_text().strip()
    try:
        authorize(desk_url, secret, pr=0, head=head, handle=handle, gap=gap,
                  run_id=run_id, statement=statement, kind=kind, module=module)
    except DeskRefused as error:
        reason = f"Task desk refused authorization: {error}"
        record_refusal(db, job_id, reason)
        if desk_url:
            _safe_desk_call(
                report_diagnostic, desk_url, secret,
                gap=gap, head=head, run_id=run_id, diagnostic=reason,
            )
        shutil.rmtree(bundle_dir, ignore_errors=True)
        raise ProofRefused(reason) from None

    stage1_passed = False
    fast_track = False
    has_kproof = (work / "proof.kproof").is_file()
    if has_kproof and kproof_worker is not None:
        try:
            kproof_worker.verify_kproof(file, work, base / "lean", toolchain, ownership_check)
        except ProofRejected as err:
            reason = str(err)
            if desk_url:
                if classify_kproof_rejection(reason) == "tamper":
                    _safe_desk_call(
                        report_moderation, desk_url, secret,
                        kind="tamper", handle=handle, github_uid=github_uid,
                        run_id=run_id, gap=gap, head=head, detail=reason,
                    )
                else:
                    _safe_desk_call(
                        report_diagnostic, desk_url, secret,
                        gap=gap, head=head, run_id=run_id, diagnostic=reason,
                    )
            shutil.rmtree(bundle_dir, ignore_errors=True)
            enqueue(db, {"lemma_id": gap, "kind": kind, "module": module, "head_sha": head,
                         "verdict": "REJECTED", "manifest": None, "run_id": run_id, "run_attempt": 1})
            return run_id
        finally:
            (bundle_dir / "proof.kproof").unlink(missing_ok=True)
            (work / "proof.kproof").unlink(missing_ok=True)

        stage1_passed = True
        throttled = bool(ticket.get("throttled"))
        if desk_url:
            kv = _safe_desk_call(report_kernel_verified, desk_url, secret, run_id=run_id, gap=gap, head=head)
            if isinstance(kv, dict) and kv.get("throttled"):
                throttled = True
        fast_track = not throttled
    else:
        (bundle_dir / "proof.kproof").unlink(missing_ok=True)
        (work / "proof.kproof").unlink(missing_ok=True)

    slot_guard = nullcontext() if (fast_track or slow_slots is None) else slow_slots
    with slot_guard:
        try:
            manifest = verify(file, work, base / "lean", toolchain, ownership_check,
                              on_container=on_container, cancelled=cancelled)
        except ProofRejected as err:
            verdict, manifest = "REJECTED", None
            reason = str(err)
            if desk_url:
                if stage1_passed:
                    is_resource = (
                        reason.startswith("REJECTED (timeout):")
                        or reason.startswith("REJECTED (memory):")
                    )
                    if is_resource:
                        mod = _safe_desk_call(
                            report_moderation, desk_url, secret,
                            kind="stage2_resource_limit", handle=handle, github_uid=github_uid,
                            run_id=run_id, gap=gap, head=head,
                            detail=f"{reason} (Stage-1 KProof passed, Stage-2 clean-room limit exceeded)",
                        )
                        if isinstance(mod, dict):
                            note = f"{reason}\nModeration: strike {mod.get('strikes')}/5 ({mod.get('action')})."
                            _safe_desk_call(
                                report_diagnostic, desk_url, secret,
                                gap=gap, head=head, run_id=run_id, diagnostic=note,
                            )
                    else:
                        _safe_desk_call(
                            report_moderation, desk_url, secret,
                            kind="tamper", handle=handle, github_uid=github_uid,
                            run_id=run_id, gap=gap, head=head,
                            detail=f"Source/KProof mismatch: Stage-1 passed but Stage-2 failed with: {reason}",
                        )
                else:
                    _safe_desk_call(
                        report_diagnostic, desk_url, secret,
                        gap=gap, head=head, run_id=run_id, diagnostic=reason,
                    )
            shutil.rmtree(bundle_dir, ignore_errors=True)
        else:
            verdict = "ACCEPTED"
            if desk_url:
                _safe_desk_call(
                    report_diagnostic, desk_url, secret,
                    gap=gap, head=head, run_id=run_id,
                    diagnostic="ACCEPTED: authoritative clean-room Lean verification succeeded; publishing to main.",
                )

    enqueue(db, {"lemma_id": gap, "kind": kind, "module": module, "head_sha": head,
                 "verdict": verdict, "manifest": manifest, "run_id": run_id, "run_attempt": 1})
    return run_id


def judge(db, app, job_id, work, base, toolchain, ownership_check, *, desk_url, secret,
          on_revision=None, on_container=None, cancelled=None,
          submissions_dir=None, kproof_worker=None, slow_slots=None):
    row = db.execute(
        "SELECT sha,pr,trigger FROM ci_jobs WHERE id=? AND kind='authoritative'", (job_id,),
    ).fetchone()
    if row is None:
        raise ValueError("Expected a queued authoritative job")
    head, pr, trigger = row

    run_id = desk_run_id(db, job_id)
    initialize(db)
    previous = db.execute(
        "SELECT delivered FROM desk_outbox WHERE run=? AND attempt=1", (run_id,),
    ).fetchone()
    if previous is not None:
        return run_id

    bundle_match = BUNDLE_TRIGGER.fullmatch(trigger or "")
    if pr == 0 and bundle_match is not None:
        if bundle_match.group(1) != head:
            raise ValueError("Bundle trigger submission ID does not match job head")
        resolved_submissions = submissions_dir or os.environ.get("GOLDBACH_SUBMISSIONS_DIR")
        if not resolved_submissions:
            raise ValueError("Private bundle submission directory is not configured")
        return _judge_bundle(
            db, job_id, run_id, head, work, base, toolchain, ownership_check,
            desk_url=desk_url, secret=secret, submissions_dir=resolved_submissions,
            kproof_worker=kproof_worker, slow_slots=slow_slots,
            on_container=on_container, cancelled=cancelled,
        )

    if not trigger.isascii() or not trigger.isdecimal() or int(trigger) < 1:
        raise ValueError("Expected a GitHub comment ID")

    comment = None
    if app is not None and desk_url:
        comment = app.request("GET", f"{REPO}/issues/comments/{trigger}")
        initial_pull = pull_request(app, pr)
        if initial_pull["state"] == "open" and initial_pull["head"]["sha"] != head:
            if on_revision is not None:
                on_revision(pr, initial_pull["head"]["sha"])
            raise StaleDelivery("The PR revision changed before desk authorization")
        if initial_pull["state"] != "open":
            raise StaleDelivery("The PR revision changed before desk authorization")
        initial_handle = initial_pull["user"]["login"]
        command_match = COMMENT_COMMAND.fullmatch((comment.get("body") or "").strip())
        if (comment["issue_url"] != f"https://api.github.com{REPO}/issues/{pr}"
                or comment["user"]["type"] != "User"
                or comment["user"]["login"].casefold() != initial_handle.casefold()
                or command_match is None):
            raise StaleDelivery("The PR author did not authorize this proof and gap")
        if on_revision is not None:
            on_revision(pr, head)
        try:
            precheck(desk_url, secret, pr=pr, head=head, handle=initial_handle,
                     gap=command_match.group(1), run_id=run_id)
        except DeskRefused as error:
            reason = f"Task desk refused authorization: {error}"
            record_refusal(db, job_id, reason)
            raise ProofRefused(reason) from None

    try:
        file = prepare(app, pr, head, base, work)
    except ProofRefused as error:
        record_refusal(db, job_id, str(error))
        raise
    gap = (work / "gap.id").read_text().strip()
    statement = (work / "statement.txt").read_bytes()
    prepared_base = json.loads((work / "pr.json").read_text(encoding="utf-8"))["base"]
    if comment is None:
        comment = app.request("GET", f"{REPO}/issues/comments/{trigger}")
    pull = pull_request(app, pr)
    current_base = pull["base"]
    if (pull["state"] != "open" or pull["head"]["sha"] != head
            or any(current_base[field] != prepared_base[field] for field in ("sha", "ref"))
            or current_base["repo"]["full_name"] != prepared_base["repo"]["full_name"]):
        if pull["state"] == "open" and pull["head"]["sha"] != head and on_revision is not None:
            on_revision(pr, pull["head"]["sha"])
        raise StaleDelivery("The PR revision changed before desk authorization")
    handle = pull["user"]["login"]
    if (comment["issue_url"] != f"https://api.github.com{REPO}/issues/{pr}"
            or comment["user"]["type"] != "User"
            or comment["user"]["login"].casefold() != handle.casefold()
            or comment["body"].strip() != f"/goldbach-check {gap}"):
        raise StaleDelivery("The PR author did not authorize this proof and gap")
    kind = (work / "task.kind").read_text().strip()
    module = (work / "pr.module").read_text().strip()
    try:
        authorize(desk_url, secret, pr=pr, head=head, handle=handle, gap=gap,
                  run_id=run_id, statement=statement, kind=kind, module=module)
    except DeskRefused as error:
        reason = f"Task desk refused authorization: {error}"
        record_refusal(db, job_id, reason)
        raise ProofRefused(reason) from None
    slot_guard = nullcontext() if slow_slots is None else slow_slots
    with slot_guard:
        try:
            manifest = verify(file, work, base / "lean", toolchain, ownership_check,
                              on_container=on_container, cancelled=cancelled)
        except ProofRejected:
            verdict, manifest = "REJECTED", None
        else:
            verdict = "ACCEPTED"
    enqueue(db, {"lemma_id": gap, "kind": kind, "module": module, "head_sha": head,
                 "verdict": verdict, "manifest": manifest, "run_id": run_id, "run_attempt": 1})
    return run_id
