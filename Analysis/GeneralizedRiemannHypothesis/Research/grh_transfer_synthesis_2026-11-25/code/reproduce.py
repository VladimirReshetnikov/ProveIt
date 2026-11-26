#!/usr/bin/env python3
"""Replay the supplied checks while preserving the delivered certificates.

Default: source snapshot, nonabelian frame, mean-to-pointwise, joint filters,
and selected CM input checks.
Optional --full-census replays both complete paired-norm searches and the
explicit-formula/table checks. --lean checks the seven elementary lemmas;
it may fetch the pinned Lean/Mathlib dependencies. --pdf rebuilds the PDF.
Logs and a copied checking workspace go under validation/replay/.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


BASE = Path(__file__).resolve().parents[1]
CHECKS = {
    "source_snapshot": "check_source_snapshot.py",
    "nonabelian_frame": "check_nonabelian_frame.py",
    "mean_to_pointwise": "check_mean_to_pointwise.py",
    "joint_filters": "check_joint_filters.py",
    "selected_cm_inputs": "check_selected_cm_inputs.py",
}


class ReplayError(RuntimeError):
    pass


def normalized_output(path):
    """Ignore only explicitly labeled timing lines; retain all certificate data."""
    timing = re.compile(r"^\s*(?:elapsed(?: time)?|runtime|wall time|user time|sys time)\s*[:=]",
                        re.IGNORECASE)
    return "\n".join(line.rstrip() for line in path.read_text(errors="strict").splitlines()
                     if not timing.match(line)).strip()


def dependency(module, installation):
    if importlib.util.find_spec(module) is None:
        raise ReplayError(f"Missing Python dependency '{module}'. Install it with: "
                          f"{sys.executable} -m pip install {installation}")


def verify_prior_hashes(prior):
    manifest_path = prior / "validation.json"
    if not manifest_path.is_file():
        raise ReplayError(f"Missing prior validation manifest: {manifest_path}")
    manifest = json.loads(manifest_path.read_text())
    for name, expected in manifest.get("files", {}).items():
        file = prior / name
        if not file.is_file():
            raise ReplayError(f"Missing pinned census input: {file}")
        observed = hashlib.sha256(file.read_bytes()).hexdigest()
        if observed != expected:
            raise ReplayError(f"SHA-256 mismatch in census input {name}: "
                              f"expected {expected}, observed {observed}")


def copy_workspace(destination):
    def ignore(directory, names):
        excluded = {".git", ".lake", "__pycache__"}
        if Path(directory).resolve() == (BASE / "validation").resolve():
            excluded.add("replay")
        return [name for name in names if name in excluded or
                name.endswith((".aux", ".fls", ".fdb_latexmk", ".synctex.gz"))]
    shutil.copytree(BASE, destination, ignore=ignore, symlinks=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks", nargs="+", choices=list(CHECKS), default=list(CHECKS),
                        help="choose quick checks (default: all five; missing files are errors)")
    parser.add_argument("--full-census", action="store_true")
    parser.add_argument("--workers", type=int, default=4,
                        help="workers for the complete Python paired-norm search (default: 4)")
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--pdf", action="store_true")
    parser.add_argument("--log-dir", type=Path, help="new replay directory; must not already exist")
    args = parser.parse_args()
    if sys.flags.optimize:
        raise ReplayError("The arithmetic checkers use assertions. Run ordinary Python without "
                          "-O/-OO and without a nonzero PYTHONOPTIMIZE setting.")
    if args.workers < 1:
        raise ReplayError("--workers must be a positive integer.")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    run_dir = (args.log_dir or BASE / "validation/replay" / f"run-{stamp}-{os.getpid()}").resolve()
    if run_dir.exists():
        raise ReplayError(f"Replay directory already exists; choose a fresh directory: {run_dir}")
    # Reject destinations inside one of the source subtrees that would copy recursively.
    try:
        relative = run_dir.relative_to(BASE)
    except ValueError:
        relative = None
    if relative is not None and relative.parts[:2] != ("validation", "replay"):
        raise ReplayError("A replay directory inside this artifact must be beneath validation/replay/.")
    run_dir.mkdir(parents=True)
    workspace = run_dir / "workspace"
    summary = {"started_utc": stamp, "status": "running", "checks": [],
               "scope": "Downstream checks only; this does not rebuild the full upstream GRH proof."}
    summary_path = run_dir / "summary.json"

    def save():
        summary_path.write_text(json.dumps(summary, indent=2) + "\n")

    def run(name, command, cwd, expected=None):
        log = run_dir / f"{name}.log"
        print(f"[{name}] {' '.join(map(str, command))}", flush=True)
        started = time.monotonic()
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream,
                                    stderr=subprocess.STDOUT)
        record = {"name": name, "returncode": result.returncode,
                  "seconds": round(time.monotonic() - started, 3), "log": log.name,
                  "command": list(map(str, command))}
        summary["checks"].append(record)
        save()
        if result.returncode:
            tail = "\n".join(log.read_text(errors="replace").splitlines()[-20:])
            raise ReplayError(f"{name} failed with exit status {result.returncode}. "
                              f"Log: {log}\n{tail}")
        if expected is not None:
            if normalized_output(log) != normalized_output(expected):
                raise ReplayError(f"{name} ran successfully, but its output differs from "
                                  f"the delivered reference {expected.name}. Compare {log}.")
            record["matches_reference"] = str(expected.relative_to(workspace))
            save()
        print(f"[{name}] passed ({record['seconds']:.3f}s); log: {log}", flush=True)

    try:
        copy_workspace(workspace)
        for check in args.checks:
            script = workspace / "code" / CHECKS[check]
            if not script.is_file():
                raise ReplayError(f"Missing required checker: {script}. "
                                  "Use a complete archive or select an explicit --checks subset.")
            if check == "nonabelian_frame":
                dependency("sympy", "sympy")
            run(check, [sys.executable, str(script)], workspace)
        if args.full_census:
            prior = workspace / "prior/exponent_six"
            verify_prior_hashes(prior)
            run("census_zero_test", [sys.executable, "zero_test.py"], prior,
                prior / "zero_test_replayed.txt")
            run("census_paired_norms_python",
                [sys.executable, "paired_norms.py", str(args.workers)], prior,
                prior / "paired_norms_python_replayed.txt")
            compiler = shutil.which("g++") or shutil.which("clang++")
            if not compiler:
                raise ReplayError("The independent C++ replay needs g++ or clang++ with C++17 "
                                  "and unsigned 128-bit integer support.")
            binary = run_dir / "paired_norms"
            run("census_compile_cpp", [compiler, "-O3", "-std=c++17", "paired_norms.cpp",
                                       "-o", str(binary)], prior)
            run("census_paired_norms_cpp", [str(binary), "5500", "151"], prior,
                prior / "paired_norms_cpp_replayed.txt")
            run("census_order_table", [sys.executable, "check_order_table.py",
                                       "orders-six.txt", "exponent-six.csv"], prior,
                prior / "order_table_replayed.txt")
        if args.lean:
            lake = shutil.which("lake")
            if not lake:
                raise ReplayError("The optional Lean check needs elan/Lake and the toolchain "
                                  "pinned in formalization/lean-toolchain.")
            formal = workspace / "formalization"
            if not (formal / "lakefile.toml").is_file() or not (formal / "lean-toolchain").is_file():
                raise ReplayError("The formalization is missing lakefile.toml or lean-toolchain.")
            # A prepared local package cache can be reused; otherwise Lake fetches the pins
            # into the replay workspace. Source certificates are never replaced.
            source_cache = BASE / "formalization/.lake"
            if source_cache.is_dir() and not (formal / ".lake").exists():
                (formal / ".lake").symlink_to(source_cache, target_is_directory=True)
            if not (formal / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").is_dir():
                run("lean_cache", [lake, "exe", "cache", "get"], formal)
            run("lean_core", [lake, "env", "lean", "TransferCore.lean"], formal)
        if args.pdf:
            run("pdf_build", [sys.executable, str(workspace / "code/build_pdf.py"),
                              "--log-dir", str(run_dir / "pdf-build"),
                              "--output", str(run_dir / "report.pdf")], workspace)
        summary["status"] = "passed"
        save()
        print(f"All requested checks passed. Summary: {summary_path}")
    except (ReplayError, OSError, subprocess.SubprocessError, ValueError) as error:
        summary["status"] = "failed"
        summary["error"] = str(error)
        save()
        raise ReplayError(f"{error}\nReplay summary: {summary_path}") from error


if __name__ == "__main__":
    try:
        main()
    except (ReplayError, OSError, ValueError) as error:
        print(f"REPLAY FAILED: {error}", file=sys.stderr)
        sys.exit(1)
