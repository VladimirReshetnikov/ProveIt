#!/usr/bin/env python3
"""Replay exact finite checks and optional numerical diagnostics.

Default: the harmonic compiler and sixty exact finite checks.
--all: also run every supplied numerical diagnostic, including the
       fifteen singularity-subtracted circle quadratures.
Results and individual logs are written beside the verification scripts.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
VERIFY = ROOT / "verification"

EXACT = [
    ["harmonic_power_reduce.py", "5", "--output", "power5.json"],
    ["verify_harmonic_powers.py", "--output", "exact_checks.json"],
]
NUMERIC = [
    ["check_mixed_orientation.py"],
    ["verify_multiple_resolvents.py", "--output", "multiple_resolvents.json"],
    ["check_mixed_log.py"],
    ["verify_special_mixed_log.py"],
    ["verify_collision_kernels.py"],
    ["verify_fifth_numeric.py", "--output", "numeric_fifth.json"],
    ["verify_higher_collision.py"],
]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="Run the full numerical suite too.")
    args = parser.parse_args()
    jobs = EXACT + (NUMERIC if args.all else [])
    records = []
    for job in jobs:
        print(f"Running {job[0]} ...", flush=True)
        start = time.monotonic()
        result = subprocess.run([sys.executable, *job], cwd=VERIFY, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = VERIFY / (Path(job[0]).stem + ".replay.log")
        log.write_text(result.stdout, encoding="utf-8")
        record = {"script": job[0], "arguments": job[1:],
                  "returncode": result.returncode,
                  "elapsed_seconds": round(time.monotonic() - start, 3),
                  "log": log.name}
        records.append(record)
        print(f"  exit {result.returncode}; {record['elapsed_seconds']} s", flush=True)
        if result.returncode:
            print(result.stdout[-6000:])
            break
    report = {
        "status": "passed" if len(records) == len(jobs)
                  and all(r["returncode"] == 0 for r in records) else "failed",
        "scope": "exact and numerical" if args.all else "exact finite",
        "python": platform.python_version(), "jobs": records,
        "evidence_boundary": "Analytic proofs are in the article. Numerical checks use no interval arithmetic.",
    }
    (VERIFY / "replay_summary.json").write_text(json.dumps(report, indent=2) + "\n",
                                               encoding="utf-8")
    print(json.dumps({"status": report["status"], "jobs": len(records)}, indent=2))
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
