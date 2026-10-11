#!/usr/bin/env python3
"""Replay exact certificates, with optional independent numerical diagnostics.

python verification/verify_all.py
python verification/verify_all.py --numerical

Individual programs can also be run separately. Results are written to the
package's results directory. No web access or source repository is needed.
"""
from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

import mpmath
import sympy

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--numerical", action="store_true")
    args = parser.parse_args()
    (ROOT / "results").mkdir(exist_ok=True)
    moment = ["verify_moment_rank.py", "--max-b", "14", "--output",
              str(ROOT / "results/moment_rank_checks.json")]
    if args.numerical:
        moment.append("--numerical")
    jobs = [moment, ["verify_moment_rank_four.py", "--max-b", "14", "--output",
                     str(ROOT / "results/moment_rank_four_checks.json")],
            ["verify_general_shifted_hankel.py"], ["verify_moment_rank_six.py"],
            ["verify_order_four_tail_identity.py"], ["verify_tornheim_cubic_symbolic.py"],
            ["differential_quotient.py"], ["independent_cubic_check.py"]]
    if args.numerical:
        jobs.extend([["independent_tail_28.py"], ["differential_numeric.py"],
                     ["verify_tornheim_cubic_numeric.py"]])
    records = []
    for job in jobs:
        print(f"Running {job[0]}", flush=True)
        start = time.monotonic()
        proc = subprocess.run([sys.executable, str(ROOT / "verification" / job[0]),
                               *job[1:]], cwd=ROOT, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        log = ROOT / "results" / (Path(job[0]).stem + ".log")
        log.write_text(proc.stdout)
        row = {"program": job[0], "arguments": job[1:],
               "return_code": proc.returncode, "seconds": round(elapsed, 3)}
        records.append(row)
        print(f"{'PASS' if proc.returncode == 0 else 'FAIL'}: {job[0]} ({elapsed:.1f}s)",
              flush=True)
        if proc.returncode:
            print(proc.stdout[-8000:])
            raise SystemExit(proc.returncode)
    report = {"status": "PASS", "numerical_included": args.numerical,
              "python": platform.python_version(), "sympy": sympy.__version__,
              "mpmath": mpmath.__version__, "programs": records}
    name = "replay_all.json" if args.numerical else "replay_exact.json"
    (ROOT / "results" / name).write_text(json.dumps(report, indent=2) + "\n")
    print(f"All requested checks passed. Recorded {name}", flush=True)


if __name__ == "__main__":
    main()
