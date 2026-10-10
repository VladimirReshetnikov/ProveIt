#!/usr/bin/env python3
"""Replay every exact check in this report, without network access.

Run from any working directory. Diagnostics and plots are optional and are
not part of the mathematical certificates.
"""
from __future__ import annotations

import argparse
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--diagnostics", action="store_true")
    args = parser.parse_args()
    checks = [
        ("gaussian_envelope", ["code/certify_gaussian_envelope.py"]),
        ("inverse_coefficients", ["code/verify_inverse.py"]),
        ("cyclic_smith", ["code/cyclic_prime_checks.py"]),
        ("lerch_endpoint_signs", ["code/lerch/certify_shape.py"]),
        ("s6_integer_separator", ["code/s6/verify_s6_separator.py", "--receipt",
                                  "results/s6/verification_receipt.json"]),
    ]
    if args.diagnostics:
        checks += [
            ("gaussian_diagnostics", ["code/gaussian_diagnostics.py"]),
            ("lerch_minimum_diagnostic", ["code/lerch/minimum_diagnostic.py"]),
            ("lerch_plot_diagnostic", ["code/lerch/plot_diagnostic.py"]),
        ]
    receipts = []
    transcript = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for name, argv in checks:
        print(f"Running {name} ...", flush=True)
        start = time.monotonic()
        proc = subprocess.run([sys.executable, *argv], cwd=ROOT, env=env,
                              capture_output=True, text=True)
        transcript.append(f"CHECK {name}\n{proc.stdout}{proc.stderr}\n")
        (ROOT / "results/replay_log.txt").write_text("\n".join(transcript))
        receipts.append({"check": name, "command": ["python", *argv],
                         "returncode": proc.returncode,
                         "elapsed_seconds": round(time.monotonic()-start, 3)})
        print(f"{name}: {'PASS' if proc.returncode == 0 else 'FAIL'}", flush=True)
        if proc.returncode:
            print(proc.stdout, proc.stderr)
            break
    versions = {"python": sys.version.split()[0]}
    for name in ["sympy", "mpmath", "numpy", "scipy", "matplotlib"]:
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            pass
    report = {
        "all_passed": len(receipts) == len(checks) and all(
            r["returncode"] == 0 for r in receipts),
        "diagnostics_requested": args.diagnostics,
        "versions": versions, "checks": receipts,
        "logical_scope": "See article: exact finite certificates and consistency checks, not proof-assistant formalization",
    }
    (ROOT / "results/replay_summary.json").write_text(json.dumps(report, indent=2)+"\n")
    if not report["all_passed"]:
        raise SystemExit(1)
    print("All requested checks passed.", flush=True)


if __name__ == "__main__":
    main()
