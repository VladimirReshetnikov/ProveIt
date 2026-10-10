#!/usr/bin/env python3
"""Replay the exact certificates; optionally rerun moment diagnostics.

Run with ordinary Python (not -O): the constituent verifiers use asserts
for mathematical acceptance checks. No network or source checkout is used.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise SystemExit("Run without -O: exact acceptance assertions must be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical", action="store_true", help="also recompute 24 moment cases")
    args = parser.parse_args()
    jobs = [
        ("Euler kernel exact checks", "code/euler", ["verify_euler_domination.py"], ["euler_domination_checks.json"]),
        ("Rational universal constant", "code/euler", ["certify_rational_euler_constant.py"], ["rational_euler_constant_certificate.json"]),
        ("Narrow maximum certificate", "code/euler", ["certify_axis_maximum.py"], ["axis_maximum_certificate.json"]),
        ("Inherited global gamma slope", "code/moments", ["certify_gamma_saddle.py", "--output", "gamma_saddle_replay.json"], ["gamma_saddle_replay.json"]),
        ("Lerch finite mesh and moments", "code/lerch", ["lerch_verify_effective.py", "--max-n", "12", "--output", "lerch_effective_verification.json"], ["lerch_effective_verification.json"]),
        ("Integral shuffle matrices", "code/shuffle", ["verify_odd_inner.py"], ["odd_inner_certificate.json"]),
        ("Gaussian rational proximity", "code/gaussian", ["verify_gaussian_proximity.py", "--s12"], ["gaussian_proximity_certificate.json"]),
    ]
    if args.numerical:
        jobs.append(("Moment quadrature diagnostics", ".", ["code/moments/verify_all_ratio_moments.py", "--dps", "60", "--output", "data/all_ratio_diagnostics.json"], ["data/all_ratio_diagnostics.json"]))
    manifest = {
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version,
        "assertions_enabled": __debug__,
        "source_commit": "3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f",
        "numerical_diagnostics_requested": args.numerical,
        "dependencies": {},
        "jobs": [],
    }
    for name in ["sympy", "mpmath", "numpy", "matplotlib"]:
        try:
            manifest["dependencies"][name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            pass
    dest = ROOT / "data" / "replay_manifest.json"
    for title, cwd, command, outputs in jobs:
        print(f"Starting: {title}", flush=True)
        started = time.monotonic()
        proc = subprocess.run([sys.executable, *command], cwd=ROOT / cwd,
                              text=True, capture_output=True)
        record = {
            "name": title, "cwd": cwd, "command": ["python3", *command],
            "exit_code": proc.returncode, "elapsed_seconds": round(time.monotonic()-started, 3),
            "stdout": proc.stdout, "stderr": proc.stderr, "outputs": {},
        }
        for item in outputs:
            path = ROOT / cwd / item
            if path.is_file():
                record["outputs"][str(path.relative_to(ROOT))] = {
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "bytes": path.stat().st_size,
                }
        manifest["jobs"].append(record)
        manifest["all_passed"] = all(j["exit_code"] == 0 for j in manifest["jobs"])
        dest.write_text(json.dumps(manifest, indent=2) + "\n")
        print(f"{'PASS' if proc.returncode == 0 else 'FAIL'}: {title} ({record['elapsed_seconds']:.3f}s)", flush=True)
        if proc.returncode:
            print(proc.stdout[-4000:] + proc.stderr[-4000:], file=sys.stderr)
            raise SystemExit(proc.returncode)
    print(f"All {len(jobs)} requested replays passed; data/replay_manifest.json written.", flush=True)


if __name__ == "__main__":
    main()
