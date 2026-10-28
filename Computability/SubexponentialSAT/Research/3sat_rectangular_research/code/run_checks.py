#!/usr/bin/env python3
"""Run the self-contained mathematical certificates; no external packages.

The programs check finite certificates and a SAT encoding. They do not
implement the complete subexponential SAT contractor or imported matrix schemes.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--optimized", action="store_true",
                        help="Run each certificate with Python -O")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    checks = [
        ("verify_new_backend.py", "new_backend_verification.json"),
        ("verify_weighted_ten.py", "weighted_ten_verification.json"),
        ("verify_schedule.py", "schedule_results.json"),
        ("verify_packing_gates.py", "packing_gate_results.json"),
        ("verify_normalization.py", "normalization_results.json"),
    ]
    results = root / "results"
    results.mkdir(exist_ok=True)
    receipts = []
    for program, filename in checks:
        command = [sys.executable]
        if args.optimized:
            command.append("-O")
        command.append(str(root / "code" / program))
        completed = subprocess.run(command, check=True, capture_output=True,
                                   text=True, cwd=root)
        data = json.loads(completed.stdout)
        if str(data.get("status", "")).lower() not in ("pass", "passed"):
            raise RuntimeError(f"Missing success status from {program}")
        rendered = json.dumps(data, indent=2, sort_keys=True) + "\n"
        if args.optimized:
            baseline = results / filename
            if baseline.exists() and json.loads(baseline.read_text()) != data:
                raise RuntimeError(f"Optimized output differs: {program}")
            filename = filename.replace(".json", "_optimized.json")
        destination = results / filename
        destination.write_text(rendered, encoding="utf-8")
        receipts.append({"program": program, "status": "PASS",
                         "result": str(destination.relative_to(root))})
        print(f"PASS {program}", flush=True)
    receipt = {"status": "PASS", "optimized": args.optimized,
               "python": sys.version.split()[0], "checks": receipts,
               "scope": "Finite certificates and normalization only; no full SAT solver."}
    name = "run_checks_optimized.json" if args.optimized else "run_checks.json"
    (results / name).write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"All {len(checks)} checks passed.", flush=True)


if __name__ == "__main__":
    main()
