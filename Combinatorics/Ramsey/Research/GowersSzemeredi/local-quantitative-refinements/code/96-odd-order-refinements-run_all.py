#!/usr/bin/env python3
"""Run the five standard-library verification programs from this package.

Each program writes its exact certificate to ../data. Its combined stdout
and stderr are captured in a separate *_run.txt log. This runner records
exit codes, elapsed wall-clock times, and Python and runner versions, then
returns a nonzero exit status if any program failed.
"""
from __future__ import annotations

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time


RUNNER_VERSION = "1.0"
PROGRAMS = (
    ("affine_completion_verify.py", "affine_completion_checks.json"),
    ("affine_weighted_verify.py", "affine_weighted_checks.json"),
    ("verify_arrangement_erasures.py", "arrangement_erasure_validation.json"),
    ("verify_odd_arrangement_repair.py", "odd_arrangement_validation.json"),
    ("verify_norm.py", "norm_certificate.json"),
)


def utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def main():
    if not __debug__:
        raise SystemExit("Run without Python -O/-OO; mathematical assertions must be active.")
    code_dir = Path(__file__).resolve().parent
    data_dir = code_dir.parent / "data"
    data_dir.mkdir(parents=True, exist_ok=True)
    started_utc = utc_now()
    all_started = time.perf_counter()
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONHASHSEED"] = "0"
    records = []
    for filename, certificate in PROGRAMS:
        log_name = Path(filename).stem + "_run.txt"
        command = [sys.executable, "-B", filename]
        print(f"Running {filename}; log: data/{log_name}", flush=True)
        started = time.perf_counter()
        with (data_dir / log_name).open("w", encoding="utf-8") as log:
            completed = subprocess.run(
                command,
                cwd=code_dir,
                env=environment,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
        elapsed = time.perf_counter() - started
        record = {
            "program": filename,
            "command": command,
            "exit_code": completed.returncode,
            "runtime_seconds": round(elapsed, 6),
            "log": "data/" + log_name,
            "certificate": "data/" + certificate,
        }
        records.append(record)
        outcome = "PASS" if completed.returncode == 0 else "FAIL"
        print(f"{outcome}: {filename} ({elapsed:.3f} s)", flush=True)
    passed = all(record["exit_code"] == 0 for record in records)
    summary = {
        "runner_version": RUNNER_VERSION,
        "python_version": platform.python_version(),
        "python_implementation": platform.python_implementation(),
        "python_full_version": sys.version,
        "platform": platform.platform(),
        "assertions_enabled": __debug__,
        "started_utc": started_utc,
        "finished_utc": utc_now(),
        "total_runtime_seconds": round(time.perf_counter() - all_started, 6),
        "programs": records,
        "status": "PASS" if passed else "FAIL",
        "all_programs_passed": passed,
        "scope": "Finite exact consistency checks supplement the written universal proofs.",
    }
    destination = data_dir / "verification_summary.json"
    destination.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"{summary['status']}: {len(records)} programs; summary: data/verification_summary.json", flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
