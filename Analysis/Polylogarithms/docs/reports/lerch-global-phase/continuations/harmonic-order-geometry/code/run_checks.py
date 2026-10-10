#!/usr/bin/env python3
"""Replay research checks, preserving a readable log and structured result.

Default: exact polynomial/interval engines and diagonal model diagnostics.
--numeric also repeats the full harmonic quadratures (can take minutes).
--figures regenerates the three publication figures from their inputs.
"""
from pathlib import Path
import argparse
import importlib.metadata
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numeric", action="store_true")
    parser.add_argument("--figures", action="store_true")
    args = parser.parse_args()
    (ROOT / "logs").mkdir(exist_ok=True)
    (ROOT / "data").mkdir(exist_ok=True)
    jobs = [
        ("diagonal_exact", ["code/verify_diagonal.py"]),
        ("harmonic_exact", ["code/verify_gaussian_order.py",
                            "--output", "data/gaussian_exact.json"]),
        ("barrier_certificates", ["code/verify_optimal_barrier.py",
                                  "--output", "data/optimal_barrier_verification.json"]),
        ("diagonal_quantitative", ["code/diagonal_quantitative.py"]),
    ]
    if args.numeric:
        jobs.append(("harmonic_numeric", ["code/verify_gaussian_order.py",
            "--numeric", "--full", "--dps", "45",
            "--output", "data/gaussian_order_verification.json"]))
    if args.figures:
        jobs.extend([
            ("harmonic_figure", ["code/plot_gaussian_order.py"]),
            ("barrier_figure", ["code/plot_barrier.py"]),
            ("diagonal_figure", ["code/plot_diagonal.py"]),
        ])
    report = {
        "python": platform.python_version(),
        "platform": platform.platform(),
        "packages": {p: importlib.metadata.version(p)
                     for p in ["mpmath", "sympy", "numpy", "scipy", "matplotlib"]},
        "requested_full_harmonic_numerics": args.numeric,
        "requested_figures": args.figures,
        "checks": [],
        "scope": "Finite identities and interval certificates plus explicitly numerical diagnostics; analytic theorems are proved in the article.",
    }
    for name, arguments in jobs:
        start = time.monotonic()
        print(f"Running {name} ...", flush=True)
        with (ROOT / "logs" / f"{name}.txt").open("w") as log:
            result = subprocess.run([sys.executable, *arguments], cwd=ROOT,
                                    stdout=log, stderr=subprocess.STDOUT)
        row = {"name": name, "arguments": arguments,
               "exit_code": result.returncode,
               "elapsed_seconds": round(time.monotonic()-start, 3)}
        report["checks"].append(row)
        (ROOT/"logs"/"verification_run.json").write_text(json.dumps(report, indent=2)+"\n")
        if result.returncode:
            print(f"FAILED: see logs/{name}.txt", file=sys.stderr)
            return result.returncode
        print(f"Passed {name} ({row['elapsed_seconds']} s).", flush=True)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
