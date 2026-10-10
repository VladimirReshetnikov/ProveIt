#!/usr/bin/env python3
"""Run the supplied proof replays and numerical diagnostics.

The expensive certificate discovery is optional and intentionally excluded.
No network or repository access is required.
"""
from __future__ import annotations

import json
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise RuntimeError("Run verification without Python's -O option.")
    jobs = [
        ("Gaussian exact certificate", ["code/verify_s4.py", "results/S4_certificate.json"]),
        ("Complement classification and plastic identities", ["code/certify_ladders.py", "--bound", "30", "--degree-limit", "12", "--out", "results"]),
        ("Reflected gamma moments", ["code/verify_reflected_moments.py"]),
        ("Independent Gaussian quadrature", ["code/check_s4_numeric.py"]),
        ("Proportional harmonic depth", ["code/verify_saddle.py"]),
    ]
    records = []
    for label, arguments in jobs:
        print(f"Checking: {label}", flush=True)
        started = time.monotonic()
        result = subprocess.run([sys.executable, *arguments], cwd=ROOT,
                                text=True, capture_output=True)
        record = {"name": label, "command": ["python", *arguments],
                  "exit_code": result.returncode,
                  "elapsed_seconds": round(time.monotonic()-started, 3)}
        if result.returncode:
            record.update(stdout=result.stdout, stderr=result.stderr)
        elif arguments[0] == "code/verify_s4.py":
            exact = json.loads(result.stdout)
            (ROOT/"results/S4_verification.json").write_text(
                json.dumps(exact, indent=2, sort_keys=True)+"\n")
            record["verification"] = exact
        records.append(record)
        print("Passed." if result.returncode == 0 else "FAILED.", flush=True)
        if result.returncode:
            break
    report = {
        "status": "passed" if len(records) == len(jobs) and all(
            row["exit_code"] == 0 for row in records) else "failed",
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "scope": "Exact finite replays plus high-precision diagnostics; analytic proofs are in the article.",
        "jobs": records,
    }
    out = ROOT/"results/verification_receipt.json"
    out.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": report["status"], "jobs": len(records),
                      "receipt": str(out.relative_to(ROOT))}, indent=2))
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
