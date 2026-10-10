#!/usr/bin/env python3
"""Replay the research certificates without overwriting delivered receipts.

Exact and interval assertions live in the individual readable verifiers.
Some verifiers also run explicitly marked floating-point regression checks;
those diagnostics do not strengthen the logical status of any claim.
"""
from __future__ import annotations

import argparse
import importlib.metadata
import json
import platform
from pathlib import Path
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=None,
                        help="Fresh replay directory (default: package/replay).")
    parser.add_argument("--diagnostics", action="store_true",
                        help="Also rerun the slower fold and conjecture diagnostics.")
    args = parser.parse_args()
    code = Path(__file__).resolve().parent
    dest = (args.output or code.parent / "replay").resolve()
    dest.mkdir(parents=True, exist_ok=True)
    for source in code.glob("*.py"):
        if source.name != Path(__file__).name:
            shutil.copy2(source, dest/source.name)
    tasks = [
        ("formal ranks and integer invariant factors", "verify_rank.py",
         ["--max-weight", "13", "--smith-max-weight", "12"]),
        ("mixed-color integer row certificates", "verify_mixed_family.py", []),
        ("modular weight polynomials and coefficient certificates",
         "modular_weight_polynomials.py", []),
        ("CM interval coefficient certificates", "cm_norms.py", []),
        ("fifth-index and third-index rational signs", "certify_n5_zeros.py", []),
        ("small-Lerch-parameter rational signs", "certify_lerch_splitting.py", []),
    ]
    if (dest/"cm_genus.py").exists():
        tasks.append(("CM genus factor and ratio certificates", "cm_genus.py", []))
    if (dest/"verify_genus_arithmetic.py").exists():
        tasks.append(("independent rational quadratic-field certificates",
                      "verify_genus_arithmetic.py", []))
    if args.diagnostics:
        tasks += [
            ("numerical fold diagnostic", "lerch_fold_diagnostic.py", []),
            ("numerical sixth/seventh-index conjectures", "explore_n6_n7.py", []),
        ]
    results = []
    for description, filename, extra in tasks:
        print(f"VERIFY: {description}", flush=True)
        start = time.monotonic()
        process = subprocess.run([sys.executable, str(dest/filename), *extra],
                                 cwd=dest, text=True, capture_output=True)
        (dest/(Path(filename).stem + ".log")).write_text(
            process.stdout + process.stderr)
        result = {
            "task": description,
            "script": filename,
            "command_arguments": extra,
            "exit_code": process.returncode,
            "elapsed_seconds": round(time.monotonic()-start, 3),
            "status": "PASS" if process.returncode == 0 else "FAIL",
        }
        results.append(result)
        print(json.dumps(result), flush=True)
        if process.returncode:
            print(process.stdout + process.stderr, file=sys.stderr)
            break
    versions = {}
    for name in ("mpmath", "sympy", "matplotlib"):
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = "not installed"
    report = {
        "status": "PASS" if all(r["exit_code"] == 0 for r in results)
                              and len(results) == len(tasks) else "FAIL",
        "python": platform.python_version(),
        "versions": versions,
        "numerical_diagnostics_requested": args.diagnostics,
        "tasks": results,
        "scope": "A successful replay verifies the assertions in each script; "
                 "the article supplies the all-index proofs and the analytic "
                 "contracts for the interval certificates.",
    }
    target = dest/"verification_summary.json"
    target.write_text(json.dumps(report, indent=2)+"\n")
    print(f"{report['status']}: {target}", flush=True)
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
