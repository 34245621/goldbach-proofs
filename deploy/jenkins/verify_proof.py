"""Compile a prepared proof and verify its statement in a separate sandbox."""

import os
import re
import secrets
import selectors
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from threading import Lock
from types import SimpleNamespace

from lean_dep_cache import OUTSIDE_IMPORT, compile_cached, context as cache_context, key as cache_key, store_cached
from verdict_manifest import MODULE, PROOF_MODULE, build_manifest, module_path

PROOF_CPUS = 4
DEPENDENCY_COMPILE_SECONDS = 15 * 60
SUBMISSION_COMPILE_SECONDS = 20 * 60
KPROOF_CHECK_SECONDS = 30
KPROOF_MAX_REUSE = 100
KPROOF_LARGE_RECYCLE_BYTES = 16 * 1024 * 1024
KPROOF_MAX_AGE_SECONDS = 30 * 60
IMAGE = "docker.m.daocloud.io/jenkins/jenkins@sha256:4d85f6cf5a8939647921564952d12a5a761f32a3bc520c2f4e5c3cafa7ea660f"
TAMPER_KPROOF_REJECTIONS = (
    "REJECTED (sorry):",
    "REJECTED (axiom):",
    "REJECTED (kproof):",
    "REJECTED (reserved-name):",
    "REJECTED (redeclares):",
    "REJECTED (not-a-project-module):",
)


def classify_kproof_rejection(reason):
    text = str(reason or "").strip()
    if any(text.startswith(prefix) for prefix in TAMPER_KPROOF_REJECTIONS):
        return "tamper"
    return "ordinary"


class ProofRejected(ValueError):
    """The trusted verifier returned a proof rejection."""


class ProofCancelled(RuntimeError):
    """An in-flight proof check was cancelled because a newer revision superseded it."""


def verifier_manifest(result, module, proof, read_source, kind="check"):
    if result.returncode == 124:
        raise ProofRejected("REJECTED (timeout): kernel verification exceeded the 20-minute time limit")
    if result.returncode == 137:
        raise ProofRejected("REJECTED (memory): kernel verification exceeded the 16 GiB memory or time limit")
    lines = (result.stdout or "").splitlines()
    if result.returncode == 1 and lines and re.match(r"^REJECTED \([a-z-]+\): ", lines[-1]):
        raise ProofRejected(lines[-1])
    result.check_returncode()
    return build_manifest(result.stdout, module, proof, read_source, kind)


def check_cache(project, work):
    build = project / ".lake/build"
    if not (build / "bin/checklemma").is_file():
        raise FileNotFoundError("The trusted Lean cache has no checklemma executable")
    for module in (work / "base-imports.txt").read_text().splitlines():
        if not MODULE.fullmatch(module):
            raise ValueError("Invalid trusted dependency module")
        artifact = (build / "lib/lean").joinpath(*module.split(".")).with_suffix(".olean")
        if not artifact.is_file():
            raise FileNotFoundError(f"The trusted Lean cache is missing {module}")


def mode_for(work):
    kind_path = work / "task.kind"
    task_kind = kind_path.read_text().strip() if kind_path.exists() else "prove"
    return {"prove": "check", "cut": "reduce", "refute": "refute"}[task_kind]


def verify(file, work, project, toolchain, ownership_check, *, on_container=None, cancelled=None):
    kind = mode_for(work)
    check_cache(project, work)
    dependencies = (work / "outside-build-order.txt").read_text().splitlines()
    if any(not PROOF_MODULE.fullmatch(name) for name in dependencies):
        raise ValueError("Invalid outside dependency module")
    module = (work / "pr.module").read_text().strip()
    leaf = module_path(module)
    if not PROOF_MODULE.fullmatch(module) or file != "lean/" + leaf:
        raise ValueError("Invalid registered proof module or path")
    proof = work / "source"
    (proof / leaf).parent.mkdir(parents=True)
    (proof / leaf).write_bytes((work / "proof.lean").read_bytes())
    (proof / "statement.txt").write_bytes((work / "statement.txt").read_bytes())
    out = work / "build"
    out.mkdir()
    os.chown(out, 1000, 1000)
    marker = work / "marker"
    marker.touch()

    # Resolve the search path against the prepared project cache once per build.
    lean_path = subprocess.check_output(
        [str(toolchain / "bin/lake"), "env", "printenv", "LEAN_PATH"],
        cwd=project, text=True, timeout=30,
    ).strip().replace(str(project), "/project")
    flags = [
        "docker", "run", "--rm", "--pull", "never", "--runtime", "runsc",
        "--network", "none", "--read-only", "--cap-drop", "ALL",
        "--security-opt", "no-new-privileges", "--pids-limit", "128",
        "--memory", "16g", "--memory-swap", "16g", "--cpus", str(PROOF_CPUS),
        "--ulimit", "fsize=536870912:536870912", "--ulimit", "core=0:0", "--log-driver", "none",
        "--tmpfs", "/tmp:rw,nosuid,nodev,size=256m",
        "--mount", f"type=bind,source={toolchain},target=/toolchain,readonly",
        "--mount", f"type=bind,source={project},target=/project,readonly",
        "--mount", f"type=bind,source={proof},target=/input,readonly",
        "--env", f"LEAN_PATH={lean_path}", "--env", "LEAN_SYSROOT=/toolchain",
        "--env", "PATH=/toolchain/bin:/usr/bin:/bin",
    ]
    # Only the guarded closure is visible to the submission and independent replay.
    compiled = work / "compiled"
    community = compiled / "Conjectures"
    community.mkdir(parents=True)
    flags += ["--mount", f"type=bind,source={community},target=/project/.lake/build/lib/lean/Conjectures,readonly"]

    def run_sandbox(extra, *, capture=False):
        if cancelled is not None and cancelled.is_set():
            raise ProofCancelled("Proof verification cancelled by a newer pull request revision")
        name = f"goldbach-verify-{secrets.token_hex(8)}"
        cmd = (["docker", "run", "--rm", "--name", name, *flags[3:], *extra]
               if on_container is not None else [*flags, *extra])
        if on_container is not None:
            on_container(name, True)
        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE if capture else None,
                stderr=subprocess.STDOUT if capture else None,
                text=True,
            )
        finally:
            if on_container is not None:
                on_container(name, False)
        if cancelled is not None and cancelled.is_set():
            raise ProofCancelled("Proof verification cancelled by a newer pull request revision")
        return result

    def compile_module(source, seconds, *, submission=False):
        artifact = Path(source).with_suffix(".olean").name
        result = run_sandbox([
            "--mount", f"type=bind,source={out},target=/output",
            "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", str(seconds),
            "/toolchain/bin/lean", f"--threads={PROOF_CPUS}", "--root=/input", "-o", f"/output/{artifact}", f"/input/{source}",
        ], capture=submission)
        if submission:
            if result.returncode == 124:
                raise ProofRejected("REJECTED (timeout): Lean compilation exceeded the 20-minute time limit")
            if result.returncode == 137:
                raise ProofRejected("REJECTED (memory): Lean compilation exceeded the 16 GiB memory or time limit")
            if result.returncode == 1 and re.search(
                    rf"^/input/{re.escape(source)}:[0-9]+:[0-9]+: error(?:\[[^]]+\])?:",
                    result.stdout or "", re.MULTILINE):
                raise ProofRejected("Lean reported a compilation error in the submitted file")
        result.check_returncode()
        subprocess.run([
            "bash", str(ownership_check), str(out), str(marker), str(out / artifact), "0", "1000",
        ], check=True, timeout=30)
        destination = compiled / Path(source).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        (out / artifact).replace(destination)

    cache_dir = os.environ.get("GOLDBACH_LEAN_DEP_CACHE")
    cache = Path(cache_dir) if cache_dir else None
    context = cache_context(project, work, f"goldbach-olean-v2:{IMAGE}:{PROOF_CPUS}".encode()) if cache else None
    keys = {}
    for name in dependencies:
        source = module_path(name)
        content = (project / source).read_bytes()
        (proof / source).parent.mkdir(parents=True, exist_ok=True)
        (proof / source).write_bytes(content)
        if cache is None:
            compile_module(source, DEPENDENCY_COMPILE_SECONDS)
            continue
        keys[name] = cache_key(context, name, content, keys)
        artifact = compiled / Path(source).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        compile_cached(cache, name, keys[name], artifact,
                       lambda: compile_module(source, DEPENDENCY_COMPILE_SECONDS))
    compile_module(leaf, SUBMISSION_COMPILE_SECONDS, submission=True)
    verification = run_sandbox([
        "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", str(SUBMISSION_COMPILE_SECONDS),
        "/project/.lake/build/bin/checklemma", module, "/input/statement.txt", kind,
    ], capture=True)

    def read_source(name):
        return project.joinpath(*name.split(".")).with_suffix(".lean").read_bytes()

    proof_bytes = (proof / leaf).read_bytes()
    manifest = verifier_manifest(verification, module, proof_bytes, read_source, kind)
    if (cache is not None and kind == "check"
            and not module.startswith("Conjectures.Cuts.Assembly")
            and all(name.decode("ascii") in keys for name in OUTSIDE_IMPORT.findall(proof_bytes))):
        leaf_artifact = compiled / Path(leaf).with_suffix(".olean")
        leaf_kproof = out / Path(leaf).with_suffix(".kproof").name
        if leaf_artifact.is_file():
            export = run_sandbox([
                "--mount", f"type=bind,source={out},target=/output",
                "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", "120",
                "/project/.lake/build/bin/checklemma", "--export-kproof", module, f"/output/{leaf_kproof.name}",
            ], capture=True)
            kproof_ready = None
            if export.returncode == 0 and leaf_kproof.is_file():
                subprocess.run([
                    "bash", str(ownership_check), str(out), str(marker), str(leaf_kproof), "0", "1000",
                ], check=True, timeout=30)
                kproof_ready = leaf_kproof
            store_cached(
                cache,
                module,
                cache_key(context, module, proof_bytes, keys),
                leaf_artifact,
                kproof_artifact=kproof_ready,
            )
            leaf_kproof.unlink(missing_ok=True)
    return manifest


class KProofWorker:
    """Persistent runsc CheckLemma --serve-kproof worker for fast Stage-1 kernel verification."""

    def __init__(self, stage_root=None):
        self._lock = Lock()
        self._proc = None
        self._container_name = None
        self._project_key = None
        self._requests = 0
        self._started_at = 0.0
        self._stage_root_arg = Path(stage_root) if stage_root else None
        self.stage_root = None

    def _ensure_stage_root(self):
        if self.stage_root is not None and self.stage_root.is_dir():
            return self.stage_root
        if self._stage_root_arg is not None:
            try:
                self._stage_root_arg.mkdir(mode=0o755, parents=True, exist_ok=True)
                os.chmod(self._stage_root_arg, 0o755)
                self.stage_root = self._stage_root_arg
                return self.stage_root
            except OSError:
                pass
        self.stage_root = Path(tempfile.mkdtemp(prefix="goldbach-kproof-stage-"))
        os.chmod(self.stage_root, 0o755)
        return self.stage_root

    def _stop_locked(self):
        proc, name = self._proc, self._container_name
        self._proc = None
        self._container_name = None
        self._project_key = None
        self._requests = 0
        if proc is not None:
            try:
                if proc.stdin:
                    proc.stdin.write(b"QUIT\n")
                    proc.stdin.flush()
            except OSError:
                pass
            try:
                proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                proc.kill()
        if name:
            subprocess.run(
                ["docker", "rm", "-f", name],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=15,
            )

    def close(self):
        with self._lock:
            self._stop_locked()

    @staticmethod
    def _read_line(stdout_fd, buf, deadline):
        while b"\n" not in buf:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("Timed out waiting for CheckLemma kproof daemon")
            with selectors.DefaultSelector() as sel:
                sel.register(stdout_fd, selectors.EVENT_READ)
                if not sel.select(remaining):
                    raise TimeoutError("Timed out waiting for CheckLemma kproof daemon")
            chunk = os.read(stdout_fd, 65536)
            if not chunk:
                raise RuntimeError("CheckLemma kproof daemon closed stdout unexpectedly")
            buf.extend(chunk)
        idx = buf.index(b"\n")
        line = bytes(buf[:idx]).decode("utf-8", errors="replace")
        del buf[:idx + 1]
        return line

    def _ensure_started_locked(self, project, toolchain):
        checklemma = project / ".lake/build/bin/checklemma"
        stat = checklemma.stat()
        key = (str(toolchain), stat.st_ino, stat.st_mtime_ns, stat.st_size)
        now = time.monotonic()
        if (self._proc is not None and self._proc.poll() is None
                and self._project_key == key and self._requests < KPROOF_MAX_REUSE
                and now - self._started_at < KPROOF_MAX_AGE_SECONDS):
            return
        self._stop_locked()
        lean_path = subprocess.check_output(
            [str(toolchain / "bin/lake"), "env", "printenv", "LEAN_PATH"],
            cwd=project, text=True, timeout=30,
        ).strip().replace(str(project), "/project")
        name = f"goldbach-kproof-{secrets.token_hex(8)}"
        cmd = [
            "docker", "run", "-i", "--rm", "--name", name, "--pull", "never", "--runtime", "runsc",
            "--network", "none", "--read-only", "--cap-drop", "ALL",
            "--security-opt", "no-new-privileges", "--pids-limit", "128",
            "--memory", "16g", "--memory-swap", "16g", "--cpus", str(PROOF_CPUS),
            "--ulimit", "core=0:0", "--log-driver", "none",
            "--tmpfs", "/tmp:rw,nosuid,nodev,size=128m",
            "--mount", f"type=bind,source={toolchain},target=/toolchain,readonly",
            "--mount", f"type=bind,source={project},target=/project,readonly",
            "--mount", f"type=bind,source={self.stage_root},target=/stage,readonly",
            "--env", f"LEAN_PATH={lean_path}", "--env", "LEAN_SYSROOT=/toolchain",
            "--env", "PATH=/toolchain/bin:/usr/bin:/bin",
            IMAGE, "/project/.lake/build/bin/checklemma", "--serve-kproof",
        ]
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        buf = bytearray()
        try:
            ready = self._read_line(proc.stdout.fileno(), buf, time.monotonic() + 60.0)
            if ready.strip() != "READY":
                raise RuntimeError(f"Unexpected kproof daemon greeting: {ready!r}")
        except BaseException:
            proc.kill()
            subprocess.run(["docker", "rm", "-f", name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=15)
            raise
        self._proc = proc
        self._container_name = name
        self._project_key = key
        self._requests = 0
        self._started_at = time.monotonic()
        self._stdout_buf = buf

    def _prepare_dep_kproofs(self, dependencies, work, project, toolchain, ownership_check, req_dir):
        if not dependencies:
            return []
        lean_path = subprocess.check_output(
            [str(toolchain / "bin/lake"), "env", "printenv", "LEAN_PATH"],
            cwd=project, text=True, timeout=30,
        ).strip().replace(str(project), "/project")
        proof = work / "kproof-deps-src"
        compiled = work / "kproof-deps-compiled"
        out = work / "kproof-deps-out"
        proof.mkdir(exist_ok=True)
        out.mkdir(exist_ok=True)
        os.chown(out, 1000, 1000)
        marker = work / "kproof-marker"
        marker.touch()
        flags = [
            "docker", "run", "--rm", "--pull", "never", "--runtime", "runsc",
            "--network", "none", "--read-only", "--cap-drop", "ALL",
            "--security-opt", "no-new-privileges", "--pids-limit", "128",
            "--memory", "16g", "--memory-swap", "16g", "--cpus", str(PROOF_CPUS),
            "--ulimit", "fsize=536870912:536870912", "--ulimit", "core=0:0", "--log-driver", "none",
            "--tmpfs", "/tmp:rw,nosuid,nodev,size=256m",
            "--mount", f"type=bind,source={toolchain},target=/toolchain,readonly",
            "--mount", f"type=bind,source={project},target=/project,readonly",
            "--mount", f"type=bind,source={proof},target=/input,readonly",
            "--mount", f"type=bind,source={out},target=/output",
            "--env", f"LEAN_PATH={lean_path}", "--env", "LEAN_SYSROOT=/toolchain",
            "--env", "PATH=/toolchain/bin:/usr/bin:/bin",
        ]
        for root in ("PEqualNP/Outside", "Conjectures"):
            (compiled / root).mkdir(parents=True, exist_ok=True)
            flags += ["--mount", f"type=bind,source={compiled / root},target=/project/.lake/build/lib/lean/{root},readonly"]

        cache_dir = os.environ.get("GOLDBACH_LEAN_DEP_CACHE")
        cache = Path(cache_dir) if cache_dir else None
        context = cache_context(project, work, f"goldbach-olean-v2:{IMAGE}:{PROOF_CPUS}".encode()) if cache else None
        keys = {}
        staged_deps = []
        for idx, name in enumerate(dependencies):
            source = module_path(name)
            content = (project / source).read_bytes()
            (proof / source).parent.mkdir(parents=True, exist_ok=True)
            (proof / source).write_bytes(content)
            olean_dest = compiled / Path(source).with_suffix(".olean")
            olean_dest.parent.mkdir(parents=True, exist_ok=True)
            kproof_dest = req_dir / f"dep_{idx}.kproof"

            def build_olean(src=source, dest=olean_dest):
                art_name = Path(src).with_suffix(".olean").name
                subprocess.run([
                    *flags, "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10",
                    str(DEPENDENCY_COMPILE_SECONDS),
                    "/toolchain/bin/lean", f"--threads={PROOF_CPUS}", "--root=/input",
                    "-o", f"/output/{art_name}", f"/input/{src}",
                ], check=True)
                subprocess.run([
                    "bash", str(ownership_check), str(out), str(marker), str(out / art_name), "0", "1000",
                ], check=True, timeout=30)
                (out / art_name).replace(dest)

            def build_kproof(mod_name=name, kp_dest=kproof_dest):
                kp_name = kp_dest.name
                subprocess.run([
                    *flags, "--entrypoint", "/usr/bin/timeout", IMAGE, "--kill-after=10", "120",
                    "/project/.lake/build/bin/checklemma", "--export-kproof", mod_name, f"/output/{kp_name}",
                ], check=True)
                subprocess.run([
                    "bash", str(ownership_check), str(out), str(marker), str(out / kp_name), "0", "1000",
                ], check=True, timeout=30)
                (out / kp_name).replace(kp_dest)
                os.chmod(kp_dest, 0o644)

            if cache is None:
                build_olean()
                build_kproof()
            else:
                keys[name] = cache_key(context, name, content, keys)
                compile_cached(
                    cache, name, keys[name], olean_dest, build_olean,
                    kproof_artifact=kproof_dest, build_kproof=build_kproof,
                )
                os.chmod(kproof_dest, 0o644)
            staged_deps.append(f"/stage/{req_dir.name}/{kproof_dest.name}")
        return staged_deps

    def verify_kproof(self, file, work, project, toolchain, ownership_check):
        kind = mode_for(work)
        check_cache(project, work)
        dependencies = (work / "outside-build-order.txt").read_text().splitlines()
        if any(not PROOF_MODULE.fullmatch(name) for name in dependencies):
            raise ValueError("Invalid outside dependency module")
        module = (work / "pr.module").read_text().strip()
        leaf = module_path(module)
        if not PROOF_MODULE.fullmatch(module) or file != "lean/" + leaf:
            raise ValueError("Invalid registered proof module or path")
        leaf_kproof = work / "proof.kproof"
        if not leaf_kproof.is_file():
            raise FileNotFoundError("Missing leaf kproof file")
        leaf_size = leaf_kproof.stat().st_size

        stage_root = self._ensure_stage_root()
        req_dir = Path(tempfile.mkdtemp(prefix="req-", dir=stage_root))
        os.chmod(req_dir, 0o755)
        try:
            dep_container_paths = self._prepare_dep_kproofs(
                dependencies, work, project, toolchain, ownership_check, req_dir,
            )
            stmt_stage = req_dir / "statement.txt"
            shutil.copyfile(work / "statement.txt", stmt_stage)
            os.chmod(stmt_stage, 0o644)
            leaf_stage = req_dir / "leaf.kproof"
            try:
                os.link(leaf_kproof, leaf_stage)
            except OSError:
                shutil.copyfile(leaf_kproof, leaf_stage)
            os.chmod(leaf_stage, 0o644)

            req_line = "\t".join([
                module,
                f"/stage/{req_dir.name}/statement.txt",
                kind,
                f"/stage/{req_dir.name}/leaf.kproof",
                ",".join(dep_container_paths),
            ]) + "\n"

            with self._lock:
                self._ensure_started_locked(project, toolchain)
                proc = self._proc
                buf = self._stdout_buf
                self._requests += 1
                try:
                    proc.stdin.write(req_line.encode("utf-8"))
                    proc.stdin.flush()
                    deadline = time.monotonic() + KPROOF_CHECK_SECONDS
                    header = self._read_line(proc.stdout.fileno(), buf, deadline)
                    match = re.fullmatch(r"BEGIN_RESULT ([0-9]+) ([0-9]+)", header.strip())
                    if not match:
                        raise RuntimeError(f"Malformed kproof result header: {header!r}")
                    code, count = int(match[1]), int(match[2])
                    out_lines = [self._read_line(proc.stdout.fileno(), buf, deadline) for _ in range(count)]
                    footer = self._read_line(proc.stdout.fileno(), buf, deadline)
                    if footer.strip() != "END_RESULT":
                        raise RuntimeError(f"Malformed kproof result footer: {footer!r}")
                except TimeoutError:
                    self._stop_locked()
                    raise ProofRejected("REJECTED (timeout): fast kernel replay exceeded the 30-second limit") from None
                except BaseException:
                    self._stop_locked()
                    raise
                if leaf_size > KPROOF_LARGE_RECYCLE_BYTES or self._requests >= KPROOF_MAX_REUSE:
                    self._stop_locked()
        finally:
            shutil.rmtree(req_dir, ignore_errors=True)

        stdout_text = ("\n".join(out_lines) + "\n") if out_lines else ""

        def check_rc():
            if code != 0:
                raise subprocess.CalledProcessError(code, "checklemma --serve-kproof", output=stdout_text)

        result = SimpleNamespace(returncode=code, stdout=stdout_text, check_returncode=check_rc)

        def read_source(name):
            return project.joinpath(*name.split(".")).with_suffix(".lean").read_bytes()

        proof_bytes = (work / "proof.lean").read_bytes()
        return verifier_manifest(result, module, proof_bytes, read_source, kind)
