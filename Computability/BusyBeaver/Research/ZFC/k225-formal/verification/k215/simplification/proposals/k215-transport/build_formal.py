#!/usr/bin/env python3
"""Fresh, sequential kernel build of the compact K215/CM215 proof packet.

No precompiled .olean/.vo file is copied.  The complete inherited baseline
endpoint is deliberately outside this small build: its uncompiled import
adapter is retained separately under integration/.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


REFERENCE_MODULES = [
    "BusyBeaver/Core.lean",
    "BusyBeaver/ZFC/KZip.lean",
    "BusyBeaver/ZFC/KTableCore.lean",
    "BusyBeaver/ZFC/KTable215.lean",
    "BusyBeaver/ZFC/KDenseBridge.lean",
    "BusyBeaver/ZFC/KDense215.lean",
]
NEW_MODULES = [
    "PositiveStutter.lean", "CM215Tables.lean", "CM215Invariant.lean",
    "CM215Transfer.lean", "CM215CoreBridge.lean", "CM215Dense.lean",
]
EXPECTED_REPORTS = {
    "PositiveStutter.lean": [
        "PositiveStutter.Simulation.halts_iff",
        "PositiveStutter.Simulation.nonhalting_iff"],
    "CM215Transfer.lean": [
        "CM215.all_tapes_halts_iff", "CM215.all_tapes_nonhalting_iff",
        "CM215.calibration_transfer"],
    "CM215CoreBridge.lean": ["CM215.CoreBridge.old_blank_iff"],
    "CM215Dense.lean": [
        "CM215.CoreBridge.core_blank_halts_iff",
        "CM215.CoreBridge.core_nonhalting_iff",
        "CM215.CoreBridge.calibration_transfer"],
}
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def executable(value):
    found = shutil.which(value)
    if found is None:
        raise RuntimeError(f"Compiler or checker not found: {value}")
    return str(Path(found).resolve())


def detect_packet_root():
    for candidate in Path(__file__).resolve().parents:
        if (candidate / "formal/CM215Tables.lean").is_file():
            return candidate
    raise RuntimeError("Pass --packet-root: cannot locate the formal/ directory")


@contextmanager
def build_lock(path):
    """Coordinate resource-heavy proof builds on POSIX; builds are always serial."""
    try:
        import fcntl
    except ImportError:
        yield
        return
    with open(path, "a", encoding="utf-8") as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def run_logged(command, *, cwd, env, log, timeout):
    started = time.monotonic()
    try:
        proc = subprocess.run(command, cwd=cwd, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=timeout, check=False)
        output, code = proc.stdout, proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = exc.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        output += "\nBUILD_DRIVER_TIMEOUT\n"
        code = 124
    log.write_text(output, encoding="utf-8")
    return {"command": command, "returncode": code,
            "seconds": round(time.monotonic()-started, 6),
            "log": str(log.relative_to(cwd))}, output


def axiom_reports(text):
    result = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        result[name] = [x.strip() for x in axioms.split(",") if x.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        result[name] = []
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--packet-root", type=Path)
    ap.add_argument("--out", type=Path, required=True, help="Fresh, nonexistent build directory")
    ap.add_argument("--lean", default="lean", help="Lean executable (tested: 4.32.0)")
    ap.add_argument("--lean-memory-mb", type=int, default=3072,
                    help="Lean memory cap in MiB (default: 3072; 2048 can be too tight)")
    ap.add_argument("--coqc", help="Optional coqc executable for the generic Rocq theorem")
    ap.add_argument("--coqchk", help="Optional recursive kernel checker; requires --coqc")
    ap.add_argument("--timeout", type=int, default=600, help="Per-module timeout in seconds")
    ap.add_argument("--lock", default="/tmp/proveit-k215-proof-build.lock")
    args = ap.parse_args()
    if args.coqchk and not args.coqc:
        ap.error("--coqchk requires --coqc")
    if args.timeout <= 0:
        ap.error("--timeout must be positive")
    if args.lean_memory_mb <= 0:
        ap.error("--lean-memory-mb must be positive")
    packet = (args.packet_root or detect_packet_root()).resolve()
    out = args.out.resolve()
    if out.exists():
        ap.error("--out must not already exist; this prevents stale compiled imports")
    lean = executable(args.lean)
    coqc = executable(args.coqc) if args.coqc else None
    coqchk = executable(args.coqchk) if args.coqchk else None
    out.mkdir(parents=True)
    (out / "logs").mkdir()
    env = os.environ.copy()
    env["LEAN_PATH"] = str(out)
    receipt = {
        "status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
        "packet_root": str(packet), "build_directory": str(out),
        "lean_executable": lean, "lean_modules": [], "axiom_reports": {},
        "build_options": {"lock": args.lock, "module_timeout_seconds": args.timeout,
                          "lean_jobs": 1, "lean_memory_mb": args.lean_memory_mb},
        "scope": "12 Lean modules; optional generic Rocq proof; full baseline endpoint not rebuilt",
    }
    receipt_path = out / "build_receipt.json"
    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    save()
    try:
        with build_lock(args.lock):
            version_run, version = run_logged([lean, "--version"], cwd=out, env=env,
                log=out/"logs/lean-version.log", timeout=60)
            if version_run["returncode"]:
                raise RuntimeError("Lean --version failed")
            receipt["lean_version"] = version.strip()
            sources = [("formal/reference/"+m, m) for m in REFERENCE_MODULES]
            sources += [("formal/"+m, m) for m in NEW_MODULES]
            for src_rel, target_rel in sources:
                src = packet/src_rel
                target = out/target_rel
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(src, target)
                assert digest(src) == digest(target)
                print(f"Compiling {target_rel}", flush=True)
                record, output = run_logged(
                    [lean, "-j1", f"-M{args.lean_memory_mb}", "-o", str(target.with_suffix(".olean")), str(target)],
                    cwd=out, env=env,
                    log=out/"logs"/(target_rel.replace("/", "_")+".log"), timeout=args.timeout)
                record.update(source=src_rel, source_sha256=digest(src))
                receipt["lean_modules"].append(record)
                save()
                if record["returncode"]:
                    raise RuntimeError(f"Lean failed on {target_rel}; see {record['log']}")
                record["object_sha256"] = digest(target.with_suffix(".olean"))
                reports = axiom_reports(output)
                for required in EXPECTED_REPORTS.get(target_rel, []):
                    if required not in reports:
                        raise RuntimeError(f"Missing axiom report: {required}")
                for theorem, axioms in reports.items():
                    if set(axioms)-ALLOWED_AXIOMS:
                        raise RuntimeError(f"Unexpected axioms in {theorem}: {axioms}")
                if "sorryAx" in output or "ofReduceBool" in output:
                    raise RuntimeError(f"Forbidden proof assumption in {target_rel}")
                receipt["axiom_reports"].update(reports)
                save()
            if coqc:
                rocq = out/"rocq"
                rocq.mkdir()
                source = packet/"formal/PositiveStutter.v"
                target = rocq/source.name
                shutil.copyfile(source, target)
                version_run, version = run_logged([coqc, "--version"], cwd=out, env=env,
                    log=out/"logs/rocq-version.log", timeout=60)
                if version_run["returncode"]:
                    raise RuntimeError("coqc --version failed")
                receipt["rocq_executable"] = coqc
                receipt["rocq_version"] = version.strip()
                print("Compiling generic Rocq theorem", flush=True)
                started = time.monotonic()
                proc = subprocess.run([coqc, "-q", target.name], cwd=rocq, env=env,
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    timeout=args.timeout, check=False)
                (out/"logs/PositiveStutter.v.log").write_text(proc.stdout, encoding="utf-8")
                receipt["rocq"] = {"source_sha256": digest(source),
                    "command": [coqc,"-q",target.name], "returncode": proc.returncode,
                    "seconds": round(time.monotonic()-started,6),
                    "log":"logs/PositiveStutter.v.log"}
                save()
                if proc.returncode or "Axioms:" in proc.stdout or proc.stdout.count("Closed under the global context") < 2:
                    raise RuntimeError("Rocq proof or closed-assumptions check failed")
                receipt["rocq"]["object_sha256"] = digest(target.with_suffix(".vo"))
                if coqchk:
                    print("Checking generic Rocq theorem with coqchk", flush=True)
                    started = time.monotonic()
                    proc = subprocess.run([coqchk,"-silent","PositiveStutter"], cwd=rocq, env=env,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        timeout=args.timeout, check=False)
                    (out/"logs/coqchk.log").write_text(proc.stdout, encoding="utf-8")
                    receipt["coqchk"] = {"executable":coqchk,
                        "command":[coqchk,"-silent","PositiveStutter"],"returncode":proc.returncode,
                        "seconds":round(time.monotonic()-started,6),"log":"logs/coqchk.log"}
                    save()
                    if proc.returncode:
                        raise RuntimeError("coqchk failed")
        receipt["status"] = "PASS"
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(f"PASS: {receipt_path}", flush=True)
    except Exception as exc:
        receipt["status"] = "FAIL"
        receipt["error"] = str(exc)
        save()
        raise


if __name__ == "__main__":
    main()
