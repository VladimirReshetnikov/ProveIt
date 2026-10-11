#!/usr/bin/env python3
"""Replay every independent check and record process completion.

Numerical checks are floating-point diagnostics, not interval certificates.
Run from any working directory. Use --jobs 1 for minimum peak resource use.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = [
    "verify_stieltjes_directions.py",
    "verify_directional_finite_parts.py",
    "verify_moving_zeros.py",
    "check_shifted_gap.py",
    "validate_anomaly.py",
    "check_vandermonde_alternants.py",
]


def run_one(name):
    start = time.monotonic()
    proc = subprocess.run(
        [sys.executable, str(ROOT / "verification" / name)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (ROOT / "results" / (Path(name).stem + ".log")).write_text(proc.stdout)
    return {"script": name, "return_code": proc.returncode,
            "seconds": round(time.monotonic() - start, 3)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    (ROOT / "results").mkdir(exist_ok=True)
    records = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = [pool.submit(run_one, name) for name in SCRIPTS]
        for future in as_completed(pending):
            row = future.result()
            records.append(row)
            print(json.dumps(row), flush=True)
    records.sort(key=lambda row: SCRIPTS.index(row["script"]))
    report = {"completed_utc": datetime.now(timezone.utc).isoformat(),
              "python": sys.version, "processes": records,
              "all_passed": all(row["return_code"] == 0 for row in records),
              "status": "Exact algebra plus floating-point diagnostics; no interval certificates."}
    (ROOT / "results" / "replay_summary.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["all_passed"]:
        sys.exit(1)


if __name__ == "__main__":
    main()

