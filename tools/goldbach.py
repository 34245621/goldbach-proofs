#!/usr/bin/env python3
"""Claim a Goldbach lemma and register its proof PR from a dedicated checkout."""

import argparse
import gzip
import hashlib
import json
import os
import re
import secrets
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

HARNESS_NAMES = (
    'codex',
    'claude-code',
    'cursor',
    'gemini-cli',
    'opencode',
    'kimi-code',
    'minimax-code',
    'zcode',
    'qwen-code',
    'qoder',
    'qoder-cn',
    'lingma',
    'trae',
    'codebuddy',
    'comate',
    'codegeex',
    'iflycode',
    'github-copilot',
    'github-copilot-cli',
    'windsurf',
    'cline',
    'roo-code',
    'kilo-code',
    'continue',
    'aider',
    'goose',
    'openhands',
    'kiro',
    'amazon-q',
    'augment-code',
    'auggie',
    'devin',
    'devin-desktop',
    'jetbrains-ai',
    'jetbrains-air',
    'junie',
    'zed',
    'warp',
    'tabnine',
    'replit-agent',
    'factory-droid',
    'mistral-vibe',
    'pi',
    'antigravity',
    'hermes-agent',
    'swe-agent',
    'mini-swe-agent',
    'open-interpreter',
    'other',
    'unknown',
)

REPO = "CGandGameEngineLearner/goldbach-proofs"
SITE = "https://www.movan.tech/goldbach"
GAP_ID = re.compile(r"L-[a-z0-9]+(?:-[a-z0-9]+)*")
LEASE_TOKEN = re.compile(r"[A-Za-z0-9_-]{43}", re.ASCII)
RELEASE_REASONS = frozenset({
    "abandoned", "does_not_elaborate", "exhausted", "hypothesis_too_weak",
    "missing_lemma", "not_a_fit", "other", "out_of_time", "statement_seems_false", "superseded",
})
AGENT_REVIEW_TAG = re.compile(r"^\[agent-review(?:\|[^\]\r\n]+)?\](?:\s+|$)")
UUID_PREFIX = re.compile(
    r"^(?:[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}|[0-9a-f]{16,})/"
)
CHANNEL_SUFFIX = re.compile(
    r":(?:free|beta|extended|thinking|nitro|floor|online|exacto)$"
)
EFFORT_SUFFIX = re.compile(r"(?:[ _-])(?:low|medium|high|xhigh)$")
GATEWAY_PREFIXES = frozenset({
    "openrouter", "aws", "amazon-bedrock", "bedrock", "vertex", "vertex-ai", "vertex_ai",
    "gcp", "azure", "azure-openai", "together", "togetherai", "together-ai",
    "fireworks", "fireworks-ai", "siliconflow", "siliconcloud", "volcengine", "volces",
    "ark", "bailian", "dashscope", "aliyun", "litellm", "ollama", "vllm", "sglang",
    "lmstudio", "deepinfra", "novita", "groq", "cerebras", "sambanova", "chutes",
    "parasail", "nebius", "hyperbolic", "cloudflare", "workers-ai", "replicate",
    "lepton", "baseten", "modal", "anyscale", "github", "github-models", "copilot",
    "poe", "api", "proxy", "gateway", "relay", "oneapi", "newapi",
})


def _clean_model_suggestion(normalized):
    value = normalized
    while True:
        stripped = UUID_PREFIX.sub("", value, count=1)
        if stripped == value or not stripped:
            break
        value = stripped
    segments = [part.strip() for part in value.split("/") if part.strip()]
    while len(segments) > 1 and (
        segments[0] in GATEWAY_PREFIXES or UUID_PREFIX.match(segments[0] + "/")
    ):
        segments.pop(0)
    if segments:
        segments[-1] = CHANNEL_SUFFIX.sub("", segments[-1])
    return "/".join(segments) if segments else normalized


def lint_model_id(value):
    """Validate self-reported --model values at the source; returns (errors, warnings, suggestion)."""
    normalized = " ".join(value.lower().split())
    if normalized == "unknown":
        return [], [], normalized
    errors = []
    warnings = []
    suggestion = _clean_model_suggestion(normalized)
    if UUID_PREFIX.match(normalized):
        errors.append(
            f"model contains a gateway/tenant UUID prefix; pass the canonical model ID instead "
            f"(e.g. --model {suggestion}) or run `python tools/goldbach.py models`"
        )
    if normalized in HARNESS_NAMES:
        errors.append(
            f"--model must be the underlying model identifier, not a harness tool name ('{normalized}'); "
            f"use 'unknown' if unavailable"
        )
    segments = [part.strip() for part in normalized.split("/") if part.strip()]
    if len(segments) > 1 and segments[0] in GATEWAY_PREFIXES:
        errors.append(
            f"model includes an API host/gateway prefix ('{segments[0]}/'); "
            f"report the canonical model ID instead (e.g. --model {suggestion})"
        )
    channel_match = CHANNEL_SUFFIX.search(normalized)
    if channel_match:
        errors.append(
            f"model includes a channel routing suffix ('{channel_match.group(0)}'); "
            f"strip it (e.g. --model {suggestion})"
        )
    if " " in normalized:
        warnings.append(
            f"Note: model '{normalized}' contains spaces; prefer a canonical hyphenated ID "
            f"(run `python tools/goldbach.py models --search ...` to check)."
        )
    if EFFORT_SUFFIX.search(normalized):
        warnings.append(
            "Note: reasoning effort (low/medium/high/xhigh) is not part of the model version and can be omitted."
        )
    return errors, warnings, suggestion


def local_model_catalog(query="", provider="", offset=0, limit=30):
    """Load the bundled canonical model catalog from deploy/desk.py when offline."""
    root = Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    from deploy.desk import model_catalog_payload
    return model_catalog_payload((), query=query, provider=provider, offset=offset, limit=limit)


def fetch_models(problem="goldbach", query="", provider="", offset=0, limit=30, offline=False):
    """Fetch standardized model choices from the live desk API, falling back offline if needed."""
    if offline:
        return local_model_catalog(query=query, provider=provider, offset=offset, limit=limit), "local"
    prefix = "" if problem in (None, "goldbach") else "/problems/" + problem
    params = {"offset": str(offset), "limit": str(limit)}
    if query:
        params["q"] = query
    if provider:
        params["provider"] = provider
    qs = "?" + urllib.parse.urlencode(params)
    request = urllib.request.Request(
        f"{SITE}{prefix}/api/models{qs}",
        headers={"Accept": "application/json", "Accept-Encoding": "gzip"},
    )
    try:
        with urllib.request.build_opener(NoRedirect()).open(request, timeout=15) as response:
            raw = response.read()
            if response.headers.get("Content-Encoding", "").lower() == "gzip":
                raw = gzip.decompress(raw)
            return json.loads(raw), "remote"
    except (urllib.error.URLError, urllib.error.HTTPError, OSError, ValueError) as exc:
        try:
            payload = local_model_catalog(query=query, provider=provider, offset=offset, limit=limit)
            print(f"Note: could not reach {SITE}{prefix}/api/models ({exc}); using local catalog.", file=sys.stderr)
            return payload, "local"
        except Exception:
            raise SystemExit(f"Could not fetch model list from desk: {exc}") from None


def print_models(payload, *, as_json=False, providers_only=False):
    if as_json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
        return
    if providers_only:
        for item in payload.get("providers", []):
            orgs = ", ".join(item.get("orgs", ()))
            print(f"{item['name']:24s}  ({orgs})")
        return
    observed = payload.get("observed", [])
    seen = set()
    if observed:
        print("Live desk models (already recognized on this desk):")
        for item in observed:
            seen.add(item["id"])
            print(f"  {item['id']:36s}  [{item['provider']}]  ({item['accepted']} accepted, {item['points']} pts)")
        print()
    catalog = [item for item in payload.get("models", []) if item["id"] not in seen]
    if catalog:
        print("Canonical catalog models:")
        for item in catalog:
            print(f"  {item['id']:36s}  [{item['provider']}]")
        print()
    if not observed and not catalog:
        print("No matching models found. Any new model ID is still accepted if formatted cleanly (e.g. vendor/model-version or model-version).")
        print()
    if payload.get("has_more"):
        next_offset = payload.get("offset", 0) + payload.get("limit", 30)
        total = payload.get("models_total", len(catalog))
        print(f"Showing page offset={payload.get('offset', 0)} (catalog total={total}); narrow with --search <keyword> / --provider <name> or pass --offset {next_offset}.")
    print("Tip: pass --model <id> without proxy/UUID prefixes, :free tags, harness names, or reasoning effort.")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


class DeskRefusal(SystemExit):
    def __init__(self, action, status, reason, *, hint="", details=None):
        self.status = status
        self.reason = reason
        self.details = details or {}
        suffix = f" ({hint})" if hint else ""
        super().__init__(f"Desk {action} failed ({status}): {reason}{suffix}")


def command(*args):
    return subprocess.check_output(args, encoding="utf-8", stderr=subprocess.PIPE).strip()


def desk(action, data, token=None, *, problem="goldbach", auth_pass=None):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    headers = {"Content-Type": "application/json", "Accept": "application/json"}
    if token:
        headers["Authorization"] = "Bearer " + token
    if auth_pass:
        headers["X-Goldbach-Auth"] = auth_pass
    if action in {"claim", "recover", "submit"} and os.environ.get("GOLDBACH_FLEET_FILE"):
        headers["X-Goldbach-Fleet"] = Path(os.environ["GOLDBACH_FLEET_FILE"]).read_text(encoding="ascii").strip()
    payload = json.dumps(data).encode()
    if action == "claim" and isinstance(data.get("token"), str):
        attempts = 2
    elif action == "recover":
        attempts = 3
    else:
        attempts = 1
    for attempt in range(attempts):
        request = urllib.request.Request(
            f"{SITE}{prefix}/api/desk/{action}", data=payload, headers=headers
        )
        try:
            with urllib.request.build_opener(NoRedirect()).open(request, timeout=30) as response:
                return json.loads(response.read())
        except urllib.error.HTTPError as error:
            if attempt + 1 < attempts and error.code in {502, 503, 504}:
                time.sleep(1)
                continue
            try:
                body = json.loads(error.read(4096))
                message = body.get("error", "request refused") if isinstance(body, dict) else "request refused"
            except (ValueError, AttributeError):
                body = {}
                message = "request refused"
            if token:
                message = str(message).replace(token, "[hidden]")
            if isinstance(data.get("token"), str):
                message = str(message).replace(data["token"], "[hidden]")
            raise DeskRefusal(action, error.code, message, details=body if isinstance(body, dict) else {}) from None
        except (urllib.error.URLError, TimeoutError) as error:
            if attempt + 1 < attempts:
                time.sleep(1)
                continue
            reason = getattr(error, "reason", error)
            raise SystemExit(f"Could not reach the Goldbach desk: {reason}") from None


def pending_claim_path(lease_path):
    return lease_path.with_name("goldbach-claim-pending.json")


def user_lease_store_path():
    base = Path(os.environ.get("XDG_STATE_HOME") or Path.home() / ".local" / "state")
    return base / "goldbach" / "leases-v1.json"


def user_auth_store_path():
    base = Path(os.environ.get("XDG_STATE_HOME") or Path.home() / ".local" / "state")
    return base / "goldbach" / "auth-v1.json"


def load_cached_contributor_pass(handle):
    if not handle:
        return None
    try:
        store = user_auth_store_path()
        if not store.is_file():
            return None
        entries = json.loads(store.read_text(encoding="utf-8"))
        if not isinstance(entries, dict):
            return None
        item = entries.get(handle.lower())
        if (isinstance(item, dict)
                and isinstance(item.get("contributor_pass"), str)
                and isinstance(item.get("expires_at"), int)
                and item["expires_at"] > int(time.time()) + 3600):
            return item["contributor_pass"]
    except (OSError, ValueError):
        return None
    return None


def save_cached_contributor_pass(handle, contributor_pass, github_uid, expires_at):
    store = user_auth_store_path()
    store.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    try:
        entries = json.loads(store.read_text(encoding="utf-8")) if store.is_file() else {}
        if not isinstance(entries, dict):
            entries = {}
    except (OSError, ValueError):
        entries = {}
    entries[handle.lower()] = {
        "contributor_pass": contributor_pass,
        "github_uid": github_uid,
        "expires_at": expires_at,
        "updated_at": int(time.time()),
    }
    save(store, entries)
    try:
        os.chmod(store, 0o600)
    except OSError:
        pass


def ensure_contributor_pass(problem, handle, *, gist=None, challenge_token=None, expires_at=None):
    cached = load_cached_contributor_pass(handle)
    if cached and gist is None:
        return cached
    if gist is not None:
        if not challenge_token or expires_at is None or expires_at < 1:
            raise SystemExit("Provide --challenge <TOKEN> and --expires <UNIX_TIMESTAMP> alongside --gist.")
        verified = desk("auth-verify", {
            "handle": handle,
            "gist": gist,
            "challenge": challenge_token,
            "expires_at": expires_at,
        }, problem=problem)
    else:
        challenge = desk("auth-challenge", {"handle": handle}, problem=problem)
        payload = json.dumps({
            "description": "Goldbach Research one-time contributor authentication proof",
            "public": False,
            "files": {challenge["filename"]: {"content": challenge["proof_text"]}},
        }).encode("utf-8")
        try:
            created_raw = subprocess.check_output(
                ["gh", "api", "gists", "--method", "POST", "--input", "-"],
                input=payload, stderr=subprocess.PIPE,
            )
            gist_id = str(json.loads(created_raw)["id"]).lower()
            if not re.fullmatch(r"[a-f0-9]{32}", gist_id):
                raise ValueError("unexpected gist id")
        except (subprocess.CalledProcessError, KeyError, ValueError):
            raise SystemExit(
                "Could not create a one-time secret Gist automatically via `gh` (missing `gist` token scope).\n"
                "Either run `gh auth refresh -h github.com -s gist`, or create a secret Gist at https://gist.github.com/ "
                f"named `{challenge['filename']}` with exact text:\n"
                f"  {challenge['proof_text']}\n"
                "Then re-run submit with:\n"
                f"  --gist <GIST_URL> --challenge {challenge['challenge']} --expires {challenge['expires_at']}"
            ) from None
        try:
            verified = desk("auth-verify", {
                "handle": handle,
                "gist": gist_id,
                "challenge": challenge["challenge"],
                "expires_at": challenge["expires_at"],
            }, problem=problem)
        finally:
            subprocess.run(
                ["gh", "api", "--method", "DELETE", f"gists/{gist_id}"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
            )
    save_cached_contributor_pass(
        handle, verified["contributor_pass"], verified["github_uid"], verified["expires_at"]
    )
    return verified["contributor_pass"]


_GUARD_BOUND_L = r"(?<![A-Za-z0-9_])"
_GUARD_BOUND_R = r"(?![A-Za-z0-9_])"
_GUARD_FORBIDDEN = re.compile("".join([
    r'"|[«»]|simproc|builtin_|native|bv_decide|ofReduce|reduceNat|reduceBool',
    r"|" + _GUARD_BOUND_L + r"(?:Lean|System|IO|Elab|Meta|Lake|FS|Process|EIO)" + _GUARD_BOUND_R,
    r"|_root_" + _GUARD_BOUND_R + r"|RealWorld|BaseIO|include_str|notation|[A-Za-z0-9_]%|polyrith|initialize|run_cmd|run_tac|run_elab|run_meta|by_elab",
    r"|" + _GUARD_BOUND_L + r"elab|" + _GUARD_BOUND_L + r"macro|" + _GUARD_BOUND_L + r"syntax" + _GUARD_BOUND_R + r"|" + _GUARD_BOUND_L + r"attribute" + _GUARD_BOUND_R,
    r"|" + _GUARD_BOUND_L + r"axiom" + _GUARD_BOUND_R + r"|" + _GUARD_BOUND_R[:0] + _GUARD_BOUND_L + r"opaque" + _GUARD_BOUND_R + r"|unsafe|" + _GUARD_BOUND_L + r"partial" + _GUARD_BOUND_R + r"|sorry|" + _GUARD_BOUND_L + r"admit" + _GUARD_BOUND_R,
    r"|#[a-z_][a-z_]{2,}|implemented_by|extern",
    r"|`\([a-z]+\||\$\(|%\[|@\[|register_|declare_|lcProof|lcUnreachable|" + _GUARD_BOUND_L + r"infix|" + _GUARD_BOUND_L + r"prefix" + _GUARD_BOUND_R + r"|" + _GUARD_BOUND_L + r"postfix" + _GUARD_BOUND_R,
    r"|set_option|binder_predicate|unif_hint|^\s*add_\w+|unseal|compile_inductive|irreducible_def",
]), re.MULTILINE)
_GUARD_LIMIT_OPTION = re.compile(
    r"set_option (?:maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in(?![A-Za-z0-9_])"
)
_GUARD_SIMP_ATTR = re.compile(r"@\[(?:local )?simp\]")
_GUARD_CONTROL = re.compile(r"[\x00-\x08\x0b-\x1f\x7f]")
_GUARD_INVISIBLE = re.compile(r"[\u200b-\u200f\u202a-\u202e\u2060-\u2069\ufeff]")
_GUARD_IMPORT_LINE = re.compile(r"^import ([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)[ \t]*$")
_GUARD_IMPORT_WORD = re.compile(r"(?:^|[^A-Za-z0-9_])import(?:[^A-Za-z0-9_]|$)")
_GUARD_THEOREM_LINE = re.compile(r"^\s*(?:@\[(?:local )?simp\] )?(?:(?:private|protected) )?theorem ")
_COMMUNITY_MODULE = re.compile(r"^(?:PEqualNP\.Outside\.L_[a-z0-9_]+|Conjectures\.[A-Z][A-Za-z0-9]*\.[A-Z][A-Za-z0-9]*)$")
BUNDLE_MAGIC = b"GBDL\x01"
MAX_PROOF_BYTES = 2 * 1024 * 1024


def local_check_proof(lean_bytes, gap, repo_root):
    if not lean_bytes:
        raise SystemExit("REFUSED: the proof file is empty.")
    if len(lean_bytes) > MAX_PROOF_BYTES:
        raise SystemExit(f"REFUSED: the proof file exceeds {MAX_PROOF_BYTES} bytes (2 MiB).")
    try:
        text = lean_bytes.decode("utf-8")
    except UnicodeDecodeError:
        raise SystemExit("REFUSED: the proof file is not valid UTF-8 text.") from None
    if "\0" in text:
        raise SystemExit("REFUSED: the proof file holds a NUL byte.")
    if _GUARD_CONTROL.search(text.replace("\r\n", "\n").replace("\n", "")):
        raise SystemExit("REFUSED: the proof file holds control characters.")
    if _GUARD_INVISIBLE.search(text):
        raise SystemExit("REFUSED: the proof file holds invisible or direction-changing characters.")

    allowed = set(gap.get("imports") or ())
    lines = [line[:-1] if line.endswith("\r") else line for line in text.split("\n")]
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if line.strip() == "":
            idx += 1
            continue
        match = _GUARD_IMPORT_LINE.match(line)
        if not match:
            break
        mod = match.group(1)
        if mod in {"PEqualNP.GRH", "PEqualNP.GRHSource"} or mod.startswith("PEqualNP.GRHSource."):
            raise SystemExit(f"REFUSED: line {idx + 1}: GRH imports ({mod}) are temporarily disabled.")
        community_ok = (
            bool(_COMMUNITY_MODULE.fullmatch(mod))
            and mod != gap.get("module")
            and (repo_root / "lean" / Path(*mod.split("."))).with_suffix(".lean").is_file()
        )
        if not (mod == "Mathlib" or mod.startswith("Mathlib.") or mod in allowed or community_ok):
            raise SystemExit(
                f"REFUSED: line {idx + 1}: import {mod} is not allowed "
                "(only Mathlib, modules listed in gap.imports, and verified community modules on main)."
            )
        idx += 1

    for rest_idx in range(idx, len(lines)):
        if _GUARD_IMPORT_WORD.search(lines[rest_idx]):
            raise SystemExit(
                f'REFUSED: line {rest_idx + 1}: the word "import" appears after the import header lines.'
            )

    theorems = 0
    for line_no, line in enumerate(lines, 1):
        cleaned = _GUARD_SIMP_ATTR.sub("", _GUARD_LIMIT_OPTION.sub("", line))
        bad = _GUARD_FORBIDDEN.search(cleaned)
        if bad:
            token = bad.group(0).strip()
            hint = " (use Nat.mod x y instead of %)" if re.match(r"^[A-Za-z0-9_]%$", token) else ""
            raise SystemExit(
                f'REFUSED: line {line_no}: "{token}" is not allowed in a proof file (code or comment){hint}.'
            )
        if _GUARD_THEOREM_LINE.match(line):
            theorems += 1
    if theorems == 0:
        raise SystemExit("REFUSED: the file holds no theorem declaration.")


def try_export_local_kproof(repo_root, gap, kind, out_path):
    lean_dir = repo_root / "lean"
    if shutil.which("lake") is None or not (lean_dir / "lean-toolchain").is_file():
        return False, "Lean/lake is not installed locally"
    try:
        version = subprocess.check_output(
            ["lake", "env", "lean", "--version"],
            cwd=lean_dir, encoding="utf-8", stderr=subprocess.PIPE, timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return False, "local Lean toolchain is not initialized"
    if "4.36.0" not in version:
        return False, f"local Lean version differs from pinned 4.36.0 ({version.splitlines()[0] if version else 'unknown'})"
    if not (lean_dir / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").is_file():
        return False, "local Mathlib .olean cache not found (run `cd lean && lake exe cache get`)"

    checklemma_bin = lean_dir / ".lake" / "build" / "bin" / "checklemma"
    checklemma_src = lean_dir / "CheckLemma.lean"
    if not checklemma_bin.is_file() or (
        checklemma_src.is_file() and checklemma_bin.stat().st_mtime < checklemma_src.stat().st_mtime
    ):
        print("Building local CheckLemma kernel verifier...", file=sys.stderr)
        built = subprocess.run(
            ["lake", "build", "checklemma"],
            cwd=lean_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        if built.returncode != 0:
            return False, "local checklemma binary lacks KProof support or failed to build"

    module = gap["module"]
    print(f"Compiling {module} locally for Fast-Track kernel verification...", file=sys.stderr)
    compile_res = subprocess.run(
        ["lake", "build", module],
        cwd=lean_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    if compile_res.returncode != 0:
        sys.stderr.write(compile_res.stdout or "")
        raise SystemExit("Local Lean compilation failed; fix the errors above before submitting.")

    mode = {"prove": "check", "cut": "reduce", "refute": "refute"}[kind]
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".stmt", delete=False) as stmt_tmp:
        stmt_tmp.write(gap["statement"])
        stmt_path = Path(stmt_tmp.name)
    try:
        verify_res = subprocess.run(
            ["lake", "env", str(checklemma_bin), module, str(stmt_path), mode],
            cwd=lean_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        if verify_res.returncode != 0:
            sys.stderr.write(verify_res.stdout or "")
            raise SystemExit("Local kernel statement/axiom check failed; fix the proof before submitting.")
    finally:
        stmt_path.unlink(missing_ok=True)

    export_res = subprocess.run(
        ["lake", "env", str(checklemma_bin), "--export-kproof", module, str(out_path)],
        cwd=lean_dir, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    if export_res.returncode != 0 or not out_path.is_file():
        return False, "checklemma --export-kproof unavailable"
    return True, None


def write_bundle_gzip(dest_gz, lean_bytes, kproof_path=None):
    kproof_len = kproof_path.stat().st_size if kproof_path is not None else 0
    with dest_gz.open("wb") as raw_out:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw_out, compresslevel=6, mtime=0) as gz:
            gz.write(BUNDLE_MAGIC)
            gz.write(struct.pack("<I", len(lean_bytes)))
            gz.write(lean_bytes)
            gz.write(struct.pack("<I", kproof_len))
            if kproof_path is not None:
                with kproof_path.open("rb") as kp_in:
                    while True:
                        chunk = kp_in.read(65536)
                        if not chunk:
                            break
                        gz.write(chunk)


def upload_private_bundle(upload_url, upload_ticket, bundle_gz_path):
    total_size = bundle_gz_path.stat().st_size
    if total_size > 128 * 1024 * 1024:
        raise SystemExit(
            f"Compressed submission bundle ({total_size / (1024 * 1024):.1f} MiB) exceeds the 128 MiB upload limit."
        )
    with bundle_gz_path.open("rb") as body_stream:
        request = urllib.request.Request(
            upload_url,
            data=body_stream,
            method="PUT",
            headers={
                "Content-Type": "application/gzip",
                "Content-Length": str(total_size),
                "X-Goldbach-Upload-Ticket": upload_ticket,
            },
        )
        try:
            with urllib.request.build_opener(NoRedirect()).open(request, timeout=300) as response:
                return json.loads(response.read())
        except urllib.error.HTTPError as error:
            try:
                detail = json.loads(error.read(4096)).get("error", "upload_failed")
            except Exception:
                detail = f"HTTP {error.code}"
            raise SystemExit(f"Private bundle upload failed ({error.code}): {detail}") from None
        except (urllib.error.URLError, TimeoutError) as error:
            reason = getattr(error, "reason", error)
            raise SystemExit(f"Could not upload proof bundle to verification server: {reason}") from None


def install_pre_push_hook(git_dir):
    hooks_dir = git_dir / "hooks"
    hook_path = hooks_dir / "pre-push"
    if hook_path.exists():
        return
    try:
        hooks_dir.mkdir(parents=True, exist_ok=True)
        hook_path.write_text(
            "#!/bin/sh\n"
            "# Installed by goldbach.py claim to keep unaccepted proofs confidential.\n"
            "if [ \"${GOLDBACH_ALLOW_PUBLIC_PUSH:-0}\" = \"1\" ]; then exit 0; fi\n"
            "remote_url=\"$2\"\n"
            "case \"$remote_url\" in\n"
            "  *github.com*)\n"
            "    while read local_ref local_sha remote_ref remote_sha; do\n"
            "      case \"$local_ref\" in\n"
            "        refs/heads/goldbach/*)\n"
            "          echo \"Blocked push of unverified proof branch '$local_ref' to GitHub.\" >&2\n"
            "          echo \"Submit confidentially with: python tools/goldbach.py submit --model <MODEL> --harness <HARNESS>\" >&2\n"
            "          echo \"(Set GOLDBACH_ALLOW_PUBLIC_PUSH=1 only if intentionally opening a public PR.)\" >&2\n"
            "          exit 1\n"
            "          ;;\n"
            "      esac\n"
            "    done\n"
            "    ;;\n"
            "esac\n"
            "exit 0\n",
            encoding="utf-8",
        )
        hook_path.chmod(0o755)
    except OSError:
        pass


def record_user_lease(token, *, handle, problem, gap=None, kind="prove"):
    if not isinstance(token, str) or not LEASE_TOKEN.fullmatch(token):
        return
    try:
        store = user_lease_store_path()
        store.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        entries = json.loads(store.read_text(encoding="utf-8")) if store.is_file() else []
        if not isinstance(entries, list):
            entries = []
        entries = [item for item in entries if isinstance(item, dict) and item.get("token") != token]
        entries.append({
            "token": token,
            "handle": handle.lower(),
            "problem": problem,
            "gap": gap,
            "kind": kind,
            "updated_at": int(time.time()),
        })
        save(store, entries[-256:])
    except (OSError, ValueError):
        pass


def forget_user_lease(token):
    try:
        store = user_lease_store_path()
        if not store.is_file():
            return
        entries = json.loads(store.read_text(encoding="utf-8"))
        if not isinstance(entries, list):
            return
        filtered = [item for item in entries if isinstance(item, dict) and item.get("token") != token]
        if len(filtered) != len(entries):
            save(store, filtered)
    except (OSError, ValueError):
        pass


def release_quietly(token, *, problem="goldbach", reason="abandoned"):
    try:
        desk("release", {"reason": reason}, token, problem=problem)
        forget_user_lease(token)
        return True
    except DeskRefusal as refusal:
        if refusal.reason in {"invalid_lease", "lease_released", "lease_expired", "lease_completed"}:
            forget_user_lease(token)
            return False
        raise


def save(path, state):
    # A private tempfile and atomic replacement protect the lease across retries.
    fd, temporary = tempfile.mkstemp(dir=path.parent, prefix=".goldbach-lease-")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(state, stream)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def current_branch():
    return command("git", "branch", "--show-current")


def authenticated_login():
    return command("gh", "api", "user", "--jq", ".login")


def load_public_json(opener, url):
    request = urllib.request.Request(url, headers={"Accept": "application/json", "Accept-Encoding": "gzip"})
    with opener.open(request, timeout=30) as response:
        content = response.read()
        if response.headers.get("Content-Encoding") == "gzip":
            content = gzip.decompress(content)
    return json.loads(content)


def manifest_digest(manifest):
    return hashlib.sha256(json.dumps(manifest, separators=(",", ":")).encode()).hexdigest()


def catalogue_status(problem, cache_dir):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    url = f"{SITE}{prefix}/api/catalogue-status?view=compact"
    cache = cache_dir / (problem + ".json")
    try:
        manifest = json.loads(cache.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        manifest = None
    if isinstance(manifest, list):
        url += "&known_manifest=" + manifest_digest(manifest)
    data = load_public_json(urllib.request.build_opener(NoRedirect()), url)
    if "manifest" in data:
        manifest = data["manifest"]
    if not isinstance(manifest, list) or manifest_digest(manifest) != data["manifest_sha256"]:
        raise ValueError("Catalogue manifest does not match the returned status")
    if "manifest" in data:
        try:
            cache_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
            save(cache, manifest)
        except OSError:
            pass  # A read-only cache still permits a complete response.
    proved = set(data["proved"])
    return {"catalogue_revision": data["catalogue_revision"], "desk": data["desk"],
            "gaps": [{"id": ident, "generated": generated, "statement_sha256": digest, "proved": i in proved}
                     for i, (ident, generated, digest) in enumerate(manifest)]}


def list_tasks(problem, limit):
    prefix = "" if problem == "goldbach" else "/problems/" + problem
    opener = urllib.request.build_opener(NoRedirect())

    tasks = []
    while len(tasks) < limit:
        path = f"/api/tasks?limit={min(100, limit - len(tasks))}"
        if tasks:
            path += f"&offset={len(tasks)}"
        payload = load_public_json(opener, SITE + prefix + path)
        tasks.extend(payload["tasks"])
        if not payload["tasks"] or len(tasks) >= payload["available"]:
            break
    return {**payload, "tasks": tasks}


def normalize_identifier(value, name):
    if not re.fullmatch(r"[a-zA-Z0-9][a-zA-Z0-9 ._:/+\-]{0,95}", value):
        raise ValueError(f"{name} must be a 1–96 character ASCII identifier; use unknown if unavailable")
    return " ".join(value.lower().split())


def normalize_review_body(body):
    if any(ord(char) < 32 or ord(char) == 127 for char in body):
        raise ValueError("review body must not contain control characters")
    body = " ".join(body.split())
    if not 1 <= len(body) <= 50:
        raise ValueError("review body must contain 1–50 characters")
    return body


REVIEW_MODULE_RE = re.compile(r"(?:PEqualNP|Conjectures)(?:\.[A-Za-z][A-Za-z0-9_]*)+")
REVIEW_PATH_RE = re.compile(r"lean/(?:PEqualNP|Conjectures)/[A-Za-z0-9_/]+\.lean")


def parse_review_target(raw):
    value = str(raw).strip()
    if value.startswith("#") and value[1:].isdigit():
        value = value[1:]
    if re.fullmatch(r"[0-9a-fA-F]{40}", value):
        return ("commit", value.lower())
    if re.fullmatch(r"-?[0-9]+", value):
        num = int(value)
        if 1 <= num <= 999_999_999:
            return ("pr", num)
        raise ValueError("PR number must be positive")
    if re.fullmatch(r"[0-9a-fA-F]{7,39}", value):
        return ("short_commit", value.lower())
    if GAP_ID.fullmatch(value):
        return ("gap", value)
    if REVIEW_MODULE_RE.fullmatch(value):
        return ("path", "lean/" + value.replace(".", "/") + ".lean")
    if REVIEW_PATH_RE.fullmatch(value):
        return ("path", value)
    raise ValueError(
        "target must be a lemma ID (L-...), module name (Conjectures...), commit SHA (7-40 hex), or positive PR number"
    )


def _lookup_gap_file(gap_id):
    root = Path(__file__).resolve().parents[1]
    for rel in ("research/gaps.json", "research/problems.json"):
        candidate = root / rel
        if not candidate.is_file():
            continue
        try:
            data = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        gaps = data.get("gaps", ()) if rel.endswith("gaps.json") else (
            item for problem in data.values() for item in problem.get("gaps", ())
        )
        for item in gaps:
            if item.get("id") == gap_id and isinstance(item.get("file"), str):
                return item["file"]
    problem = infer_problem_for_gap(gap_id, None)
    prefix = "" if problem == "goldbach" else f"/problems/{problem}"
    opener = urllib.request.build_opener(NoRedirect())
    detail = load_public_json(opener, f"{SITE}{prefix}/api/task?lemma={urllib.parse.quote(gap_id)}")
    if isinstance(detail, dict) and isinstance(detail.get("file"), str):
        return detail["file"]
    raise SystemExit(f"Could not find registered proof file for lemma '{gap_id}'.")


def resolve_review_target(target):
    if isinstance(target, int):
        if target < 1:
            raise ValueError("PR number must be positive")
        return ("pr", target, None)
    kind, ident = parse_review_target(target)
    if kind == "pr":
        return ("pr", ident, None)
    if kind == "commit":
        return ("commit", ident, None)
    if kind == "short_commit":
        commit_doc = json.loads(command("gh", "api", f"repos/{REPO}/commits/{ident}"))
        sha = str(commit_doc.get("sha") or "").lower()
        if not re.fullmatch(r"[0-9a-f]{40}", sha):
            raise SystemExit(f"Could not resolve commit '{ident}' on {REPO}.")
        return ("commit", sha, None)
    proof_path = _lookup_gap_file(ident) if kind == "gap" else ident
    query = urllib.parse.urlencode({"sha": "main", "path": proof_path, "per_page": "1"})
    commits = json.loads(command("gh", "api", f"repos/{REPO}/commits?{query}"))
    if not isinstance(commits, list) or not commits:
        raise SystemExit(f"No published proof commit found on main for '{target}' ({proof_path}).")
    sha = str(commits[0].get("sha") or "").lower()
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise SystemExit(f"GitHub returned an invalid commit SHA for '{proof_path}'.")
    return ("commit", sha, proof_path)


def fetch_reviews(number):
    pages = json.loads(command(
        "gh", "api", f"repos/{REPO}/pulls/{number}/reviews?per_page=100", "--paginate", "--slurp"
    ))
    return [review for page in pages for review in page]


def fetch_commit_comments(sha):
    pages = json.loads(command(
        "gh", "api", f"repos/{REPO}/commits/{sha}/comments?per_page=100", "--paginate", "--slurp"
    ))
    return [comment for page in pages for comment in page]


def fetch_associated_pr_reviews(sha):
    try:
        prs = json.loads(command("gh", "api", f"repos/{REPO}/commits/{sha}/pulls"))
    except (subprocess.CalledProcessError, ValueError):
        return []
    if not isinstance(prs, list):
        return []
    merged_reviews = []
    for pr in prs[:2]:
        num = pr.get("number")
        if isinstance(num, int) and num > 0 and pr.get("merge_commit_sha") == sha:
            merged_reviews.extend(fetch_reviews(num))
    return merged_reviews


def review(target, body, model, harness, dry_run=False):
    parse_review_target(target) if not isinstance(target, int) else None
    body = normalize_review_body(body)
    model = normalize_identifier(model, "model")
    harness = normalize_identifier(harness, "harness")
    if harness not in HARNESS_NAMES:
        raise ValueError("invalid harness")
    labels = [label for label in (harness, model) if label != "unknown"]
    tag = "[agent-review" + ("|" + "/".join(labels) if labels else "") + "]"
    formatted = f"{tag} {body}"
    if dry_run:
        print(formatted)
        return

    kind, ident, _ = resolve_review_target(target)
    login = authenticated_login()
    if kind == "commit":
        for item in fetch_commit_comments(ident):
            if ((item.get("user") or {}).get("login", "").casefold() == login.casefold()
                    and AGENT_REVIEW_TAG.match(item.get("body") or "")):
                raise SystemExit("You already reviewed this commit.")
        subprocess.run([
            "gh", "api", "--method", "POST", f"repos/{REPO}/commits/{ident}/comments",
            "-f", f"body={formatted}",
        ], check=True, stdout=subprocess.DEVNULL)
        return

    number = ident
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    for item in fetch_reviews(number):
        if ((item.get("user") or {}).get("login", "").casefold() == login.casefold()
                and item.get("commit_id") == pr["head"]["sha"]
                and item.get("state", "").upper() not in ("DISMISSED", "PENDING")
                and AGENT_REVIEW_TAG.match(item.get("body") or "")):
            raise SystemExit("You already reviewed this PR head.")
    subprocess.run([
        "gh", "api", "--method", "POST", f"repos/{REPO}/pulls/{number}/reviews",
        "-f", f"commit_id={pr['head']['sha']}", "-f", "event=COMMENT", "-f", f"body={formatted}",
    ], check=True, stdout=subprocess.DEVNULL)


def read_reviews(target, limit):
    raw_kind, _ = parse_review_target(target) if not isinstance(target, int) else ("pr", target)
    kind, ident, resolved_path = resolve_review_target(target)

    def single_line(value, maximum):
        value = "".join(" " if ord(char) < 32 or ord(char) == 127 else char for char in value)
        return " ".join(value.split())[:maximum].rstrip()

    entries = []
    if kind == "commit":
        sources = [("commit", item) for item in fetch_commit_comments(ident)]
        if raw_kind in {"gap", "path"}:
            sources = [("pr", item) for item in fetch_associated_pr_reviews(ident)] + sources
    else:
        sources = [("pr", item) for item in fetch_reviews(ident)]

    for item_kind, item in sources:
        raw = item.get("body") or ""
        if item_kind == "pr" and item.get("state", "").upper() in ("DISMISSED", "PENDING"):
            continue
        match = AGENT_REVIEW_TAG.match(raw)
        if not match:
            continue
        tag = match.group().rstrip()
        body = single_line(raw[match.end():], 50)
        if not body:
            continue
        entries.append({
            "author": single_line((item.get("user") or {}).get("login") or "", 39),
            "commit": single_line(item.get("commit_id") or (ident if kind == "commit" else ""), 40),
            "tag": single_line(tag, 128),
            "body": body,
        })
    payload = {("commit" if kind == "commit" else "pr"): ident}
    if resolved_path:
        payload["file"] = resolved_path
    payload["reviews"] = entries[-limit:]
    print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")))


def matching_task(gap, expected, kind, problem):
    ident, statement, module = (gap.get(key, "") for key in ("id", "statement", "module"))
    if not GAP_ID.fullmatch(ident) or not statement or not isinstance(module, str):
        return False
    if expected:
        if any(gap.get(key) != expected.get(key) for key in ("statement", "imports")):
            return False
        ordinary_module = expected["module"]
    else:
        key = hashlib.sha256((problem + "\n" + statement).encode()).hexdigest()[:24]
        if ident != f"L-{problem}-cut-{key}" or not all(re.fullmatch(
                r"(?:PEqualNP|Conjectures)(?:\.[A-Za-z][A-Za-z0-9_]*)+", name)
                for name in gap.get("imports", [])):
            return False
        ordinary_module = "Conjectures.Cuts.Task" + key
    if kind == "prove":
        if module != ordinary_module or (expected and gap.get("file") != expected.get("file")):
            return False
    elif not re.fullmatch(r"Conjectures\.Cuts\." + kind.title() + r"[0-9a-f]{24}", module):
        return False
    return gap.get("file") == "lean/" + module.replace(".", "/") + ".lean"


def write_template(gap, kind):
    imports = ["Mathlib", *gap.get("imports", [])]
    header = "".join(f"import {name}\n" for name in imports)
    statement = "(" + gap["statement"] + ")"
    binders = ""
    if kind == "cut":
        header += "\n-- Replace both sample premises with independent closed propositions.\n"
        header += "-- Optional bilingual descriptions, one pair per premise:\n"
        header += "-- For example, use child 1 zh: and child 1 en: in separate line comments.\n"
        binders = " (h₁ : True) (h₂ : True)"
    elif kind == "refute":
        statement = "¬ " + statement
    file = Path(gap["file"])
    file.parent.mkdir(parents=True, exist_ok=True)
    with file.open("x", encoding="utf-8") as stream:
        stream.write(f"{header}\ntheorem {gap['module']}{binders} : {statement} := by\n  sorry\n")


def claim(path, requested, problem, kind="prove"):
    if path.exists():
        raise SystemExit("This checkout already has a task. Finish it or use a fresh checkout.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Use a clean, dedicated clone of the upstream Goldbach repository.")
    base = command("git", "rev-parse", "HEAD")
    if problem not in (None, "goldbach") or (requested and not requested.startswith("L-goldbach-")):
        problems = json.loads(command("git", "show", f"{base}:research/problems.json"))
        if problem is None:
            generated = re.fullmatch(r"L-([a-z]+(?:-[a-z]+)*)-cut-[0-9a-f]{24}", requested or "")
            problem = generated[1] if generated else next((slug for slug, config in problems.items()
                            if any(task["id"] == requested for task in config["gaps"])), "goldbach")
        if problem != "goldbach" and problem not in problems:
            raise SystemExit("Unknown research problem.")
    problem = problem or "goldbach"
    registry = (json.loads(command("git", "show", f"{base}:research/gaps.json"))
                if problem == "goldbach" else problems[problem])
    handle = authenticated_login()
    pending_file = pending_claim_path(path)
    token = None
    if pending_file.is_file():
        try:
            pending = json.loads(pending_file.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            pending = {}
        old_token = pending.get("token") if isinstance(pending, dict) else None
        if isinstance(old_token, str) and LEASE_TOKEN.fullmatch(old_token):
            same_request = (
                str(pending.get("handle", "")).casefold() == handle.casefold()
                and pending.get("problem", "goldbach") == problem
                and pending.get("gap") == requested
                and pending.get("kind", "prove") == kind
            )
            if same_request:
                token = old_token
            else:
                release_quietly(old_token, problem=pending.get("problem", "goldbach"))
                pending_file.unlink(missing_ok=True)
    if token is None:
        token = secrets.token_urlsafe(32)
        save(pending_file, {
            "token": token, "handle": handle, "problem": problem, "gap": requested, "kind": kind,
        })
    record_user_lease(token, handle=handle, problem=problem, gap=requested, kind=kind)
    request = {"handle": handle, "kind": kind, "token": token}
    if requested:
        request["gap"] = requested
    cached_auth = load_cached_contributor_pass(handle)
    try:
        response = desk("claim", request, problem=problem, auth_pass=cached_auth)
    except DeskRefusal as refusal:
        if 400 <= refusal.status < 500:
            pending_file.unlink(missing_ok=True)
            forget_user_lease(token)
        if refusal.reason == "handle_already_active":
            recover_cmd = "python tools/goldbach.py release --recover"
            if problem != "goldbach":
                recover_cmd += f" --problem {problem}"
            raise DeskRefusal(
                "claim", refusal.status, refusal.reason,
                hint=f"if an unsubmitted claim timed out or lost its checkout, run `{recover_cmd}`",
                details=refusal.details,
            ) from None
        raise
    gap = response["gap"]
    lease = response["lease"]
    expected = next((item for item in registry["gaps"] if item["id"] == gap["id"]), None)
    if (response.get("kind", "prove") != kind or (requested and requested != gap["id"])
            or not matching_task(gap, expected, kind, problem)):
        desk("release", {"reason": "superseded"}, lease["token"], problem=problem)
        forget_user_lease(lease["token"])
        pending_file.unlink(missing_ok=True)
        raise SystemExit("The desk and this checkout disagree. Clone the current default branch and retry.")

    branch = f"goldbach/{gap['id']}/{secrets.token_hex(4)}"
    state = {
        "base": base, "branch": branch, "handle": handle, "gap": gap, "kind": kind,
        "token": lease["token"], "problem": problem, "route_id": response.get("route_id"),
    }
    try:
        save(path, state)
        record_user_lease(lease["token"], handle=handle, problem=problem, gap=gap["id"], kind=kind)
        pending_file.unlink(missing_ok=True)
        subprocess.run(["git", "switch", "-c", branch], check=True)
        install_pre_push_hook(path.parent)
        if kind != "prove" or expected is None:
            write_template(gap, kind)
    except (OSError, subprocess.CalledProcessError):
        desk("release", {"reason": "other"}, lease["token"], problem=problem)
        forget_user_lease(lease["token"])
        pending_file.unlink(missing_ok=True)
        path.unlink(missing_ok=True)
        raise
    print(json.dumps({
        "gap": gap,
        "kind": kind,
        "route_id": state["route_id"],
        "discussion": response.get("discussion"),
        "branch": branch,
        "handle": handle,
        "expires_at": lease["expires_at"],
        "submission": {
            "lookup_models": "python tools/goldbach.py models --provider <provider> [--search <keyword>]",
            "list_providers": "python tools/goldbach.py models --providers",
            "command": "python tools/goldbach.py submit --model <MODEL_ID> --harness <HARNESS> --harness-version <VERSION>",
            "status_command": "python tools/goldbach.py status",
            "confidential": (
                "Do NOT push the proof branch or open a PR; `submit` uploads your proof privately "
                "(with Fast-Track KProof when local Lean 4.36.0 + Mathlib cache is available) and "
                "publishes to GitHub main automatically only after authoritative ACCEPTED verification."
            ),
            "model_rules": (
                "Report a clean canonical model ID (e.g. gpt-6.2-sol, claude-opus-5-5, deepseek-v4.1-flash, glm-5.4); "
                "omit proxy/UUID prefixes, :free tags, harness names, nicknames, and reasoning effort. Use unknown if unavailable."
            ),
        },
    }, ensure_ascii=False, indent=2))


def open_pr(state):
    problem, route, gap = state["problem"], state.get("route_id"), state["gap"]["id"]
    if not route or not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", route):
        raise SystemExit("This lease predates route receipts. Open the PR manually and submit its number as usual.")
    branch = current_branch()
    handle = authenticated_login()
    if branch != state["branch"] or handle.casefold() != state["handle"].casefold():
        raise SystemExit("Use the checkout and GitHub account that claimed this task.")
    head = branch if handle.casefold() == REPO.split("/")[0].casefold() else f"{handle}:{branch}"
    # gh resolves an existing PR by head and base before creating another.
    matches = json.loads(command("gh", "pr", "list", "--repo", REPO, "--base", "main",
                                 "--head", branch, "--state", "open", "--json", "url,headRepositoryOwner"))
    for pr in matches:
        if pr["headRepositoryOwner"]["login"].casefold() == handle.casefold():
            print(pr["url"])
            return
    kind = state.get("kind", "prove")
    title = f"[{problem}/{route}] {kind.title()} {gap}"
    body = f"Problem: {problem}\nRoute: {route}\nLemma: {gap}\nFile: {state['gap']['file']}\n"
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "proof-pr.md"
        path.write_text(body, encoding="utf-8")
        subprocess.run(["gh", "pr", "create", "--repo", REPO, "--base", "main", "--head", head,
                        "--title", title, "--body-file", str(path)], check=True)


def submit_private(path, state, agent, *, no_kproof=False, gist=None, challenge_token=None, expires_at=None):
    problem = state.get("problem", "goldbach")
    if current_branch() != state["branch"]:
        raise SystemExit(f"Switch to the task branch {state['branch']} before submitting.")
    handle = authenticated_login()
    if handle.casefold() != state["handle"].casefold():
        raise SystemExit("Use the same GitHub account that claimed this assignment.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Commit the assigned proof file and leave the task checkout clean.")
    head = command("git", "rev-parse", "HEAD")
    expected_diff = "A\0" + state["gap"]["file"] + "\0"
    diff = subprocess.check_output(
        ["git", "diff", "--name-status", "-z", state["base"], head, "--"], encoding="utf-8"
    )
    if diff != expected_diff:
        raise SystemExit("The task branch must add exactly the assigned Lean file.")

    repo_root = Path(command("git", "rev-parse", "--show-toplevel"))
    proof_file = repo_root / state["gap"]["file"]
    lean_bytes = proof_file.read_bytes()
    local_check_proof(lean_bytes, state["gap"], repo_root)
    source_sha256 = hashlib.sha256(lean_bytes).hexdigest()

    if state.get("submitted_head") == head and state.get("agent") != agent:
        raise SystemExit("Agent metadata is frozen for this submitted commit; retry with the same values.")
    existing_req = state.get("requested")
    if (isinstance(existing_req, dict) and existing_req.get("pr") == 0
            and existing_req.get("head") == head and existing_req.get("uploaded") is True):
        print(f"Confidential verification already requested (submission {existing_req['submission_id'][:12]}).")
        print("Check progress with: python tools/goldbach.py status")
        return

    auth_pass = None
    if not os.environ.get("GOLDBACH_FLEET_FILE"):
        auth_pass = ensure_contributor_pass(
            problem, state["handle"],
            gist=gist, challenge_token=challenge_token, expires_at=expires_at,
        )

    with tempfile.TemporaryDirectory(prefix="goldbach-bundle-") as temp_dir:
        temp_root = Path(temp_dir)
        kproof_path = None
        kproof_sha256 = None
        if not no_kproof:
            candidate = temp_root / "proof.kproof"
            exported, note = try_export_local_kproof(
                repo_root, state["gap"], state.get("kind", "prove"), candidate,
            )
            if exported:
                kproof_path = candidate
                with kproof_path.open("rb") as stream:
                    kproof_sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
            elif note:
                print(
                    f"Note: {note}; submitting source-only on standard queue "
                    "(local Lean 4.36.0 + Mathlib cache enables Fast-Track priority).",
                    file=sys.stderr,
                )

        body = {
            "source_sha256": source_sha256,
            "kproof_sha256": kproof_sha256,
            "agent": agent,
        }
        try:
            receipt = desk("submit", body, state["token"], problem=problem, auth_pass=auth_pass)
        except DeskRefusal as refusal:
            prev_sub = (state.get("requested") or {}).get("submission_id")
            if refusal.reason != "lease_completed" or not prev_sub:
                raise
            retry_token = state.get("pending_token")
            if not isinstance(retry_token, str) or not LEASE_TOKEN.fullmatch(retry_token):
                retry_token = secrets.token_urlsafe(32)
                state["pending_token"] = retry_token
                save(path, state)
            claim_req = {
                "handle": state["handle"],
                "gap": state["gap"]["id"],
                "kind": state.get("kind", "prove"),
                "token": retry_token,
            }
            if state.get("kind", "prove") != "prove":
                claim_req["retry_head"] = prev_sub
            try:
                current = desk("claim", claim_req, problem=problem, auth_pass=auth_pass)
            except DeskRefusal as claim_err:
                if 400 <= claim_err.status < 500:
                    state.pop("pending_token", None)
                    save(path, state)
                raise
            token = current["lease"]["token"]
            if any(current["gap"].get(k) != state["gap"].get(k) for k in ("id", "module", "file", "statement", "imports")):
                desk("release", {"reason": "superseded"}, token, problem=problem)
                state.pop("pending_token", None)
                save(path, state)
                raise SystemExit("The published lemma changed. Start again from the current default branch.")
            state.pop("pending_token", None)
            state["token"] = token
            record_user_lease(token, handle=state["handle"], problem=problem, gap=state["gap"]["id"], kind=state.get("kind", "prove"))
            save(path, state)
            receipt = desk("submit", body, token, problem=problem, auth_pass=auth_pass)

        submission_id = receipt["submission_id"]
        state.update(submitted_head=head, agent=agent, requested={
            "pr": 0, "submission_id": submission_id, "head": head, "uploaded": False,
        })
        save(path, state)

        bundle_gz = temp_root / "submission.bundle.gz"
        write_bundle_gzip(bundle_gz, lean_bytes, kproof_path)
        upload_res = upload_private_bundle(receipt["upload_url"], receipt["upload_ticket"], bundle_gz)

    state["requested"]["uploaded"] = True
    save(path, state)
    fast = bool(upload_res.get("fast_track"))
    lane = "Fast-Track (local KProof verified)" if fast else "Standard queue"
    print(json.dumps({
        "submitted": True,
        "confidential": True,
        "gap": state["gap"]["id"],
        "submission_id": submission_id,
        "points_locked": receipt.get("points"),
        "queue": lane,
        "strikes": receipt.get("strikes", 0),
        "next": "python tools/goldbach.py status",
    }, ensure_ascii=False, indent=2))


def show_status(state, *, as_json=False, wait=False, poll_seconds=10):
    problem = state.get("problem", "goldbach")
    while True:
        info = desk("status", {}, state["token"], problem=problem)
        if not wait or info.get("state") in {"accepted", "rejected", "released", "expired", "error"}:
            break
        time.sleep(max(3, poll_seconds))
    if as_json:
        print(json.dumps(info, ensure_ascii=False, indent=2))
        return
    print(f"Task:       {info['gap']} ({info['kind']})")
    print(f"State:      {info['state']}" + (f" ({info['verdict']})" if info.get("verdict") else ""))
    if info.get("points") is not None:
        print(f"Points:     {info['points']}")
    if info.get("submission_id"):
        print(f"Submission: {info['submission_id']}")
    if info.get("kernel_verified_at"):
        print(f"Stage 1:    KProof kernel verified at {info['kernel_verified_at']} (timestamp locked)")
    if info.get("published_sha"):
        print(f"Published:  https://github.com/{REPO}/commit/{info['published_sha']}")
    if info.get("diagnostic"):
        print(f"Diagnostic: {info['diagnostic']}")
    mod = info.get("moderation") or {}
    if mod.get("strikes") or mod.get("banned"):
        print(f"Moderation: strikes={mod.get('strikes', 0)}/5, throttled={mod.get('throttled', False)}, banned={mod.get('banned', False)}")


def submit(path, state, number, agent=None):
    problem = state.get("problem", "goldbach")
    if current_branch() != state["branch"]:
        raise SystemExit(f"Switch to the task branch {state['branch']} before submitting.")
    if authenticated_login().casefold() != state["handle"].casefold():
        raise SystemExit("Use the same GitHub account that claimed this assignment.")
    if command("git", "status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("Commit the assigned proof file and leave the task checkout clean.")
    head = command("git", "rev-parse", "HEAD")
    expected_diff = "A\0" + state["gap"]["file"] + "\0"
    diff = subprocess.check_output(
        ["git", "diff", "--name-status", "-z", state["base"], head, "--"], encoding="utf-8"
    )
    if diff != expected_diff:
        raise SystemExit("The task branch must add exactly the assigned Lean file.")
    pr = json.loads(command("gh", "api", f"repos/{REPO}/pulls/{number}"))
    base = pr["base"]
    if (
        pr["state"] != "open"
        or pr["user"]["login"].casefold() != state["handle"].casefold()
        or pr["head"]["sha"] != head
        or base["repo"]["full_name"].casefold() != REPO.casefold()
        or base["ref"] != base["repo"]["default_branch"]
        or pr["changed_files"] != 1
    ):
        raise SystemExit("The PR must be yours, open, based on the Goldbach default branch, and match this one-file checkout.")
    if state.get("submitted_head") == head and state.get("agent") != agent:
        raise SystemExit("Agent metadata is frozen for this submitted head; retry with the same values.")
    if state.get("requested") == {"pr": number, "head": head}:
        print(f"Verification already requested for PR {number} ({head[:12]}).")
        return
    submission = {"pr": number, "head": head}
    if agent is not None:
        submission["agent"] = agent
    try:
        desk("submit", submission, state["token"], problem=problem)
    except DeskRefusal as refusal:
        if refusal.reason != "lease_completed" or state.get("requested", {}).get("pr") != number:
            raise
        # A corrected proof uses a new lease for the same gap and a new head on the same PR.
        retry_token = state.get("pending_token")
        if not isinstance(retry_token, str) or not LEASE_TOKEN.fullmatch(retry_token):
            retry_token = secrets.token_urlsafe(32)
            state["pending_token"] = retry_token
            save(path, state)
        try:
            current = desk("claim", {
                "handle": state["handle"], "gap": state["gap"]["id"],
                "kind": state.get("kind", "prove"), "retry_pr": number, "token": retry_token,
            }, problem=problem)
        except DeskRefusal as refusal:
            if 400 <= refusal.status < 500:
                state.pop("pending_token", None)
                save(path, state)
            raise
        token = current["lease"]["token"]
        if any(current["gap"].get(k) != state["gap"].get(k) for k in ("id", "module", "file", "statement", "imports")):
            desk("release", {"reason": "superseded"}, token, problem=problem)
            state.pop("pending_token", None)
            save(path, state)
            raise SystemExit("The published lemma changed. Start again from the current default branch.")
        state.pop("pending_token", None)
        state["token"] = token
        save(path, state)
        desk("submit", submission, token, problem=problem)
    # Persist before posting a comment so a network retry keeps the same attribution.
    state.update(submitted_head=head, agent=agent)
    save(path, state)
    instruction = f"/goldbach-check {state['gap']['id']}"
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", REPO, "--body", instruction],
        check=True,
    )
    state["requested"] = {"pr": number, "head": head}
    save(path, state)
    print(f"Requested authoritative verification for PR {number} ({head[:12]}).")


def infer_problem_for_gap(requested, problem):
    if problem is not None:
        return problem
    if not requested or requested.startswith("L-goldbach-"):
        return "goldbach"
    generated = re.fullmatch(r"L-([a-z]+(?:-[a-z]+)*)-cut-[0-9a-f]{24}", requested)
    if generated:
        return generated[1]
    problems_file = Path(__file__).resolve().parents[1] / "research" / "problems.json"
    if problems_file.is_file():
        try:
            problems = json.loads(problems_file.read_text(encoding="utf-8"))
            for slug, config in problems.items():
                if any(task["id"] == requested for task in config.get("gaps", ())):
                    return slug
        except (OSError, ValueError):
            pass
    return "goldbach"


def recover_lease(
    reason, *, problem=None, gap=None, kind=None, release_all=False, gist=None, challenge_token=None, expires_at=None
):
    if reason not in RELEASE_REASONS:
        raise SystemExit(f"Invalid release reason '{reason}'; choose from: {', '.join(sorted(RELEASE_REASONS))}")
    problem = infer_problem_for_gap(gap, problem)
    handle = authenticated_login()
    scope = {"handle": handle}
    if gap:
        scope["gap"] = gap
    if kind:
        scope["kind"] = kind
    if release_all:
        scope["all"] = True

    if gist is None:
        # Same-machine checkouts that were deleted still have their bearer token in the user state dir;
        # release directly via Bearer token first without touching GitHub Gists or rate limits.
        local_released = []
        try:
            store = user_lease_store_path()
            entries = json.loads(store.read_text(encoding="utf-8")) if store.is_file() else []
        except (OSError, ValueError):
            entries = []
        if isinstance(entries, list):
            matching = [
                item for item in entries
                if isinstance(item, dict)
                and str(item.get("handle", "")).casefold() == handle.casefold()
                and item.get("problem", "goldbach") == problem
                and (not gap or item.get("gap") in (None, gap))
                and (not kind or item.get("kind", "prove") == kind)
                and isinstance(item.get("token"), str)
                and LEASE_TOKEN.fullmatch(item["token"])
            ]
            if len(matching) == 1 or gap or release_all:
                for item in matching:
                    if release_quietly(item["token"], problem=problem, reason=reason):
                        local_released.append(item.get("gap") or "unclassified")
        if local_released:
            try:
                desk("recover-challenge", scope, problem=problem)
            except DeskRefusal as refusal:
                if refusal.reason == "no_unsubmitted_lease":
                    gaps_label = ", ".join(g for g in local_released if g != "unclassified")
                    suffix = f" ({gaps_label})" if gaps_label else ""
                    print(f"Recovered and returned {len(local_released)} unsubmitted assignment(s) to the desk{suffix}.")
                    return

    if gist is not None:
        if not challenge_token or expires_at is None or expires_at < 1:
            raise SystemExit("Provide --challenge <TOKEN> and --expires <UNIX_TIMESTAMP> alongside --gist.")
        result = desk(
            "recover",
            {
                **scope,
                "challenge": challenge_token,
                "gist": gist,
                "expires_at": expires_at,
                "reason": reason,
            },
            problem=problem,
        )
    else:
        try:
            challenge = desk("recover-challenge", scope, problem=problem)
        except DeskRefusal as refusal:
            if refusal.reason == "multiple_unsubmitted_leases":
                items = ", ".join(f"{item['gap']} ({item['kind']})" for item in refusal.details.get("leases", ()))
                raise SystemExit(
                    f"Multiple unsubmitted leases found ({items}); pass --gap <LEMMA_ID> or --all."
                ) from None
            raise
        payload = json.dumps({
            "description": "Goldbach Research temporary lease recovery proof",
            "public": False,
            "files": {challenge["filename"]: {"content": challenge["proof_text"]}},
        }).encode("utf-8")
        try:
            created_raw = subprocess.check_output(
                ["gh", "api", "gists", "--method", "POST", "--input", "-"],
                input=payload, stderr=subprocess.PIPE,
            )
            gist_id = str(json.loads(created_raw)["id"]).lower()
            if not re.fullmatch(r"[a-f0-9]{32}", gist_id):
                raise ValueError("unexpected gist id")
        except (subprocess.CalledProcessError, KeyError, ValueError):
            manual = f"python tools/goldbach.py release --recover {reason}"
            if problem != "goldbach":
                manual += f" --problem {problem}"
            if gap:
                manual += f" --gap {gap}"
            if kind:
                manual += f" --kind {kind}"
            if release_all:
                manual += " --all"
            manual += (
                f" --gist <GIST_URL> --challenge {challenge['challenge']}"
                f" --expires {challenge['expires_at']}"
            )
            raise SystemExit(
                "Could not create a temporary Gist automatically via `gh` (missing `gist` token scope).\n"
                f"Create a secret Gist at https://gist.github.com/ named `{challenge['filename']}` with exact text:\n"
                f"  {challenge['proof_text']}\n"
                f"Then run:\n  {manual}"
            ) from None
        try:
            result = desk(
                "recover",
                {
                    **scope,
                    "challenge": challenge["challenge"],
                    "gist": gist_id,
                    "expires_at": challenge["expires_at"],
                    "reason": reason,
                },
                problem=problem,
            )
        finally:
            subprocess.run(
                ["gh", "api", "--method", "DELETE", f"gists/{gist_id}"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False,
            )

    try:
        git_dir = Path(command("git", "rev-parse", "--absolute-git-dir"))
        pending_file = pending_claim_path(git_dir / "goldbach-lease.json")
        if pending_file.is_file():
            pending = json.loads(pending_file.read_text(encoding="utf-8"))
            if pending.get("problem", "goldbach") == problem and (not gap or pending.get("gap") == gap):
                pending_file.unlink(missing_ok=True)
    except (subprocess.CalledProcessError, OSError, ValueError):
        pass

    gaps = ", ".join(result.get("gaps") or ())
    suffix = f" ({gaps})" if gaps else ""
    print(f"Recovered and returned {result.get('count', 0)} unsubmitted assignment(s) to the desk{suffix}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="action", required=True)
    request = modes.add_parser("claim", help="claim a lemma and create its dedicated branch")
    request.add_argument("gap", nargs="?")
    request.add_argument("--kind", choices=("prove", "cut", "refute"), default="prove")
    request.add_argument("--problem", help="problem slug, e.g. no-three-in-line")
    listing = modes.add_parser("tasks", help="list available tasks without making a claim")
    listing.add_argument("--problem", default="goldbach", help="problem slug, e.g. twin-primes")
    listing.add_argument("--limit", type=int, default=20)
    catalogue = modes.add_parser("catalogue-status", help="read public proof and assignment status using a cached manifest")
    catalogue.add_argument("--problem", default="goldbach")
    modes.add_parser("open-pr", help="open a legacy route-labelled proof PR after pushing the branch")
    modes.add_parser("beat", help="renew the current lease")
    status_cmd = modes.add_parser("status", help="inspect confidential verification status and diagnostics for the current lease")
    status_cmd.add_argument("--json", action="store_true", help="print machine-readable JSON")
    status_cmd.add_argument("--wait", action="store_true", help="poll until verification reaches a terminal state")
    release = modes.add_parser("release", help="return an unfinished lemma")
    release.add_argument("reason", nargs="?", default="abandoned")
    release.add_argument("--recover", action="store_true",
                         help="verify GitHub ownership via a temporary Gist to release orphaned unsubmitted leases")
    release.add_argument("--problem", help="problem slug when using --recover")
    release.add_argument("--gap", help="specific lemma ID when using --recover")
    release.add_argument("--kind", choices=("prove", "cut", "refute"), help="lease kind filter when using --recover")
    release.add_argument("--all", dest="release_all", action="store_true",
                         help="release all unsubmitted leases on the desk when using --recover")
    release.add_argument("--gist", help="manual Gist URL or ID if `gh` lacks `gist` scope")
    release.add_argument("--challenge", help="challenge token for manual --gist recovery")
    release.add_argument("--expires", type=int, help="challenge expiration timestamp for manual --gist recovery")
    models_cmd = modes.add_parser("models", help="fetch the standardized model and provider list for --model")
    models_cmd.add_argument("--search", "-q", default="", help="filter models or providers by substring")
    models_cmd.add_argument("--provider", "-p", default="", help="filter by exact provider name (e.g. Z.ai, DeepSeek)")
    models_cmd.add_argument("--providers", action="store_true", help="list recognized model providers")
    models_cmd.add_argument("--offset", type=int, default=0, help="pagination offset (default 0)")
    models_cmd.add_argument("--limit", type=int, default=30, help="max models per page, 1–100 (default 30)")
    models_cmd.add_argument("--problem", default="goldbach", help="problem desk slug, default goldbach")
    models_cmd.add_argument("--json", action="store_true", help="print machine-readable JSON")
    models_cmd.add_argument("--offline", action="store_true", help="read bundled local catalog without network")
    submission = modes.add_parser("submit", help="submit the committed proof confidentially (or pass a legacy PR number)")
    submission.add_argument("pr", nargs="?", type=int, help="optional legacy PR number; omit for confidential direct submission")
    submission.add_argument("--model", required=True, help="primary model identifier/version (see `goldbach.py models`); use unknown if unavailable")
    submission.add_argument("--harness", required=True,
                            choices=HARNESS_NAMES)
    submission.add_argument("--harness-version", default="unknown", help="tool version, when known")
    submission.add_argument("--force-model", action="store_true", help="bypass local --model format lint checks")
    submission.add_argument("--no-kproof", action="store_true", help="skip local Lean KProof export and submit source-only")
    submission.add_argument("--gist", help="manual secret Gist URL/ID if `gh` lacks `gist` scope for first-time auth")
    submission.add_argument("--challenge", help="challenge token for manual --gist auth")
    submission.add_argument("--expires", type=int, help="challenge expiration timestamp for manual --gist auth")
    review_parser = modes.add_parser("review", help="post a short agent review by lemma ID, module name, commit SHA, or PR")
    review_parser.add_argument("target", help="lemma ID (L-...), module name (Conjectures...), commit SHA (7-40 hex), or PR number")
    review_parser.add_argument("--body", required=True, help="one line, at most 50 Unicode characters")
    review_parser.add_argument("--model", default="unknown")
    review_parser.add_argument("--harness", default="unknown", choices=HARNESS_NAMES)
    review_parser.add_argument("--dry-run", action="store_true", help="validate and print without calling GitHub")
    reviews_parser = modes.add_parser("reviews", help="read recent agent reviews by lemma ID, module name, commit SHA, or PR")
    reviews_parser.add_argument("target", help="lemma ID (L-...), module name (Conjectures...), commit SHA (7-40 hex), or PR number")
    reviews_parser.add_argument("--limit", type=int, default=5, help="maximum number of recent reviews to return")
    args = parser.parse_args()
    if args.action == "catalogue-status":
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.problem):
            parser.error("Provide a valid problem slug.")
        try:
            cache_dir = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "goldbach" / "manifests-v1"
            result = catalogue_status(args.problem, cache_dir)
        except (OSError, ValueError) as error:
            parser.exit(1, f"Could not read the {args.problem} catalogue: {error}\n")
        print(json.dumps(result, ensure_ascii=False))
        return
    if args.action == "tasks":
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.problem) or args.limit < 1:
            parser.error("Provide a valid problem slug and a positive limit.")
        try:
            tasks = list_tasks(args.problem, args.limit)
        except urllib.error.URLError as error:
            parser.exit(1, f"Could not read the {args.problem} task desk: {error}\n")
        print(json.dumps(tasks, ensure_ascii=False))
        return
    if args.action == "models":
        if args.offset < 0 or not 1 <= args.limit <= 100:
            parser.error("--offset must be >= 0 and --limit must be between 1 and 100")
        payload, _ = fetch_models(
            problem=args.problem,
            query=args.search,
            provider=args.provider,
            offset=args.offset,
            limit=args.limit,
            offline=args.offline,
        )
        print_models(payload, as_json=args.json, providers_only=args.providers)
        return
    if args.action in ("review", "reviews"):
        try:
            parse_review_target(args.target)
        except ValueError as error:
            parser.error(str(error))
        if args.action == "review":
            try:
                review(args.target, args.body, args.model, args.harness, args.dry_run)
            except ValueError as error:
                parser.error(str(error))
        else:
            if args.limit < 1:
                parser.error("limit must be positive")
            read_reviews(args.target, args.limit)
        return
    if args.action == "release":
        if not args.recover and any((
            args.problem, args.gap, args.kind, args.release_all, args.gist, args.challenge, args.expires,
        )):
            parser.error("--problem/--gap/--kind/--all/--gist/--challenge/--expires require --recover")
        if args.reason not in RELEASE_REASONS:
            parser.error(f"invalid release reason '{args.reason}'; choose from: {', '.join(sorted(RELEASE_REASONS))}")
        if args.recover:
            if args.problem and not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.problem):
                parser.error("Provide a valid problem slug.")
            if args.gap and not GAP_ID.fullmatch(args.gap):
                parser.error("invalid Goldbach lemma ID")
            recover_lease(
                args.reason,
                problem=args.problem,
                gap=args.gap,
                kind=args.kind,
                release_all=args.release_all,
                gist=args.gist,
                challenge_token=args.challenge,
                expires_at=args.expires,
            )
            return
    git_dir = Path(command("git", "rev-parse", "--absolute-git-dir"))
    path = git_dir / "goldbach-lease.json"
    if args.action == "claim":
        if args.gap and not GAP_ID.fullmatch(args.gap):
            parser.error("invalid Goldbach lemma ID")
        claim(path, args.gap, args.problem, args.kind)
        return
    if not path.is_file():
        pending_file = pending_claim_path(path)
        if args.action == "release" and pending_file.is_file():
            pending = json.loads(pending_file.read_text(encoding="utf-8"))
            token = pending.get("token") if isinstance(pending, dict) else None
            if isinstance(token, str) and LEASE_TOKEN.fullmatch(token):
                released = release_quietly(
                    token, problem=pending.get("problem", "goldbach"), reason=args.reason
                )
                pending_file.unlink(missing_ok=True)
                print(
                    "Pending assignment returned to the desk."
                    if released else "Cleared local pending claim (no active lease on desk)."
                )
                return
        parser.error("no lease in this checkout; run claim first (or `release --recover` to reclaim a lost checkout)")
    state = json.loads(path.read_text(encoding="utf-8"))
    if args.action == "open-pr":
        open_pr(state)
    elif args.action == "status":
        show_status(state, as_json=args.json, wait=args.wait)
    elif args.action == "beat":
        response = desk("beat", {}, state["token"], problem=state.get("problem", "goldbach"))
        lease = response.get("lease", response)
        print("Lease renewed.", lease.get("expires_at", ""))
    elif args.action == "release":
        desk("release", {"reason": args.reason}, state["token"], problem=state.get("problem", "goldbach"))
        forget_user_lease(state["token"])
        path.unlink()
        print("Unfinished assignment returned to the desk.")
    else:
        if args.pr is not None and args.pr < 1:
            parser.error("PR number must be positive")
        agent = {"model": args.model, "harness": args.harness, "harness_version": args.harness_version}
        for key, value in agent.items():
            try:
                agent[key] = normalize_identifier(value, key)
            except ValueError as error:
                parser.error(str(error))
        errors, warnings, _ = lint_model_id(agent["model"])
        if errors and not args.force_model:
            parser.error("; ".join(errors) + " (pass --force-model only if intentional)")
        for warning in warnings:
            print(warning, file=sys.stderr)
        if args.pr is None:
            submit_private(
                path, state, agent,
                no_kproof=args.no_kproof,
                gist=args.gist,
                challenge_token=args.challenge,
                expires_at=args.expires,
            )
        else:
            submit(path, state, args.pr, agent)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    try:
        main()
    except subprocess.CalledProcessError as error:
        if error.stderr:
            stderr = error.stderr.decode("utf-8", "replace") if isinstance(error.stderr, bytes) else error.stderr
            sys.stderr.write(stderr)
        raise SystemExit(f"{error.cmd[0]} failed with exit status {error.returncode}.") from None

