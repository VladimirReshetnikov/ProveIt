#!/usr/bin/env python3
"""Replay exact certificates; optionally regenerate all numerical diagnostics.

Analytic proofs and external theorems are not replaced by this finite replay.
"""
from __future__ import annotations

import argparse
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(name, *args, json_stdout=None):
    started = time.perf_counter()
    result = subprocess.run(
        [sys.executable, str(ROOT/"code"/name), *args],
        cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode:
        raise RuntimeError(name + " failed:\n" + result.stdout + result.stderr)
    if json_stdout:
        parsed = json.loads(result.stdout)
        (ROOT/json_stdout).write_text(json.dumps(parsed, indent=2)+"\n")
    elapsed = time.perf_counter()-started
    print(f"PASS {name} ({elapsed:.2f} s)", flush=True)
    return {"program": name, "arguments": list(args), "status": "PASS",
            "seconds": round(elapsed, 3), "stderr": result.stderr.strip()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerical", action="store_true",
                        help="Also run all symbolic and numerical programs")
    args = parser.parse_args()
    for directory in ("data", "verification"):
        (ROOT/directory).mkdir(exist_ok=True)
    rows = [
        run("golden_seed_certificate.py",
            json_stdout="data/golden_seed_certificate.json"),
        run("depth_s3_verify.py"),
    ]
    if args.numerical:
        rows.extend([
            run("moment_asymptotics.py", "--dps", "60"),
            run("geometry_diagnostics.py"),
            run("geometry_boundary_diagnostics.py"),
            run("canonical_reconstruction_check.py", "--dps", "160", "--terms", "600"),
        ])
    report = {
        "status": "PASS", "python": platform.python_version(),
        "mode": "exact, symbolic, and numerical" if args.numerical else "exact finite certificates",
        "programs": rows,
        "scope": "Exact finite algebra plus optional diagnostics; analytic proofs are in the article.",
        "numerical_period_independence_claimed": False,
        "S6_proved": False,
    }
    (ROOT/"verification/replay_summary.json").write_text(json.dumps(report, indent=2)+"\n")


if __name__ == "__main__":
    main()
