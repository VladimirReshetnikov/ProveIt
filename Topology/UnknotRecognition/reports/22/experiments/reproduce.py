#!/usr/bin/env python3
"""Reproduce selected checks in a separate workspace, preserving bundled data.

Run this file by absolute path from any working directory.  With no mode flag,
the quick checks run.  Full tests, the exhaustive m<=10 identity diagnostic,
and the seven-repeat capped benchmarks require explicit modes.  --all selects
all stages and may be slow.  Only the Python standard library is required.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]


def parse_arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="new test suites, finite audits and m<=4 identity checks (default)")
    parser.add_argument("--full-tests", action="store_true",
                        help="all 152 combined test methods")
    parser.add_argument("--identity", action="store_true",
                        help="exhaustive identity-family diagnostics through --max-m (default 10)")
    parser.add_argument("--benchmarks", action="store_true",
                        help="paired capped benchmarks; seven repeats by default")
    parser.add_argument("--all", action="store_true",
                        help="all stages, including full tests and benchmarks; explicitly slow")
    parser.add_argument("--max-m", type=int, default=10,
                        help="identity-mode maximum word length, 0..10 (default 10)")
    parser.add_argument("--repeats", type=int, default=7,
                        help="benchmark repeat count (default 7)")
    parser.add_argument("--seconds", type=float, default=3.0,
                        help="cooperative cap per benchmark recognition call (default 3.0)")
    parser.add_argument("--max-objects", type=int, default=20_000,
                        help="benchmark scanner object cap (default 20000)")
    parser.add_argument("--output-dir", type=Path,
                        help="new output directory; default is package/reproductions/UTC-timestamp")
    args = parser.parse_args()
    if not 0 <= args.max_m <= 10:
        parser.error("--max-m must be between 0 and 10")
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    if not math.isfinite(args.seconds) or args.seconds <= 0:
        parser.error("--seconds must be finite and positive")
    if args.max_objects < 1:
        parser.error("--max-objects must be positive")
    if not any((args.quick, args.full_tests, args.identity, args.benchmarks, args.all)):
        args.quick = True
    if args.all:
        args.quick = args.full_tests = args.identity = args.benchmarks = True
    return parser, args


def make_workspace(output):
    """Copy the frozen executables and fixtures, leaving original evidence intact."""
    output.mkdir(parents=True, exist_ok=False)
    workspace = output / "workspace"
    workspace.mkdir()
    ignore = shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo", ".pytest_cache")
    for name in ("fast", "experiments"):
        shutil.copytree(ROOT / name, workspace / name, ignore=ignore)
    for name in ("examples", "certificates"):
        source = ROOT / name
        if source.is_dir():
            shutil.copytree(source, workspace / name, ignore=ignore)
        else:
            (workspace / name).mkdir()
    (workspace / "results").mkdir()
    (output / "logs").mkdir()
    return workspace


def selected_jobs(args, workspace):
    fast, experiments = workspace / "fast", workspace / "experiments"
    jobs = []

    def script(name, *arguments):
        jobs.append((Path(name).stem, [sys.executable, str(experiments / name),
                                     *map(str, arguments)], workspace))

    if args.quick and not args.full_tests:
        for pattern in ("test_rational.py", "test_tangle_obstruction.py"):
            jobs.append((Path(pattern).stem, [sys.executable, "-m", "unittest", "discover",
                                             "-s", "tests", "-p", pattern, "-v"], fast))
    if args.full_tests:
        jobs.append(("full_tests", [sys.executable, "-m", "unittest", "discover",
                                    "-s", "tests", "-v"], fast))
    if args.quick:
        script("audit_montesinos.py")
        script("audit_subtangles.py")
        # This independently audited diagnostic is optional in early package
        # drafts.  It is run only when its portable final script is included.
        if (experiments / "verify_checkpoint_family.py").is_file():
            script("verify_checkpoint_family.py")
    if args.identity or args.quick:
        maximum = args.max_m if args.identity else min(4, args.max_m)
        output_name = "identity_verification.json" if args.identity else "identity_quick.json"
        script("verify_identity_family.py", "--max-m", maximum,
               "--output", workspace / "results" / output_name)
    if args.benchmarks:
        script("benchmark.py", "--repeats", args.repeats,
               "--seconds", args.seconds, "--max-objects", args.max_objects)
    return jobs


def main():
    parser, args = parse_arguments()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S_%fZ")
    output = (args.output_dir.expanduser().resolve() if args.output_dir
              else ROOT / "reproductions" / stamp)
    if output.exists():
        parser.error("--output-dir must be a new directory; existing results are preserved")
    for name in ("fast", "experiments", "examples", "certificates"):
        source = (ROOT / name).resolve()
        if output == source or source in output.parents:
            parser.error("--output-dir must be outside the code/fixture trees being copied")
    try:
        workspace = make_workspace(output)
    except OSError as exc:
        parser.exit(2, f"cannot create reproduction workspace: {exc}\n")

    jobs = selected_jobs(args, workspace)
    report_path = output / "reproduction_summary.json"
    report = {
        "status": "RUNNING", "python": sys.version,
        "package_root": str(ROOT), "execution_workspace": str(workspace),
        "bundled_results_modified": False,
        "modes": {name: getattr(args, name)
                  for name in ("quick", "full_tests", "identity", "benchmarks", "all")},
        "options": {name: getattr(args, name)
                    for name in ("max_m", "repeats", "seconds", "max_objects")},
        "jobs": [],
    }

    def save():
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    env = dict(os.environ)
    env.pop("PYTHONPATH", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    print("Reproduction workspace:", workspace, flush=True)
    print("Bundled results remain unchanged.", flush=True)
    print("Stages:", ", ".join(name for name, _, _ in jobs), flush=True)
    save()
    started = time.perf_counter()
    try:
        for index, (name, command, cwd) in enumerate(jobs, 1):
            log = output / "logs" / f"{index:02d}_{name}.txt"
            print(f"[{index}/{len(jobs)}] {name}; log: {log}", flush=True)
            began = time.perf_counter()
            with log.open("w", encoding="utf-8") as handle:
                handle.write("Command: " + repr(command) + "\n")
                handle.write("Working directory: " + str(cwd) + "\n\n")
                handle.flush()
                completed = subprocess.run(command, cwd=cwd, env=env,
                                           stdout=handle, stderr=subprocess.STDOUT)
            elapsed = time.perf_counter() - began
            report["jobs"].append({"name": name, "command": command, "cwd": str(cwd),
                                   "log": str(log), "exit_code": completed.returncode,
                                   "seconds": elapsed})
            save()
            print(f"  exit={completed.returncode}, elapsed={elapsed:.3f}s", flush=True)
            if completed.returncode:
                report["status"] = "FAILED"
                report["total_seconds"] = time.perf_counter() - started
                save()
                print("\n".join(log.read_text(encoding="utf-8", errors="replace")
                                .splitlines()[-12:]), file=sys.stderr)
                print("Stopped after failure; details:", report_path, file=sys.stderr)
                return completed.returncode if completed.returncode > 0 else 1
    except KeyboardInterrupt:
        report["status"] = "INTERRUPTED"
        report["total_seconds"] = time.perf_counter() - started
        save()
        print("Interrupted; partial records:", report_path, file=sys.stderr)
        return 130
    report["status"] = "PASSED"
    report["total_seconds"] = time.perf_counter() - started
    save()
    print("All selected stages passed.", flush=True)
    print("Summary:", report_path, flush=True)
    print("New raw data:", workspace / "results", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
