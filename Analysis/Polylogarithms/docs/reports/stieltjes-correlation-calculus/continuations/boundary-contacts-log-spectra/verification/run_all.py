#!/usr/bin/env python3
"""Run the exact and numerical checks, preserving separate evidence classes."""
from __future__ import annotations
import argparse
from decimal import Decimal
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def check_residuals(report: dict, threshold: str = "1e-40") -> int:
    """Enforce a conservative diagnostic tolerance on recorded residuals."""
    count = 0
    def walk(value, key=""):
        nonlocal count
        if isinstance(value, dict):
            for name, child in value.items():
                walk(child, name)
        elif isinstance(value, list):
            for child in value:
                walk(child, key)
        elif "residual" in key and isinstance(value, (str, int, float)):
            residual = Decimal(str(value))
            if not residual.is_finite() or abs(residual) >= Decimal(threshold):
                raise AssertionError(f"{key}: {residual} exceeds {threshold}")
            count += 1
    walk(report)
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-only", action="store_true")
    args = parser.parse_args()
    data = ROOT / "data"
    data.mkdir(exist_ok=True)
    jobs = [
        ["verify_contacts.py", "--output-dir", str(data)],
        ["verify_stieltjes_boundary.py", "--output-dir", str(data)],
    ]
    if args.exact_only:
        for job in jobs:
            job.append("--exact-only")
    else:
        jobs += [[name] for name in (
            "check_density_independent.py",
            "check_full_scalar_independent.py",
            "check_polylog_bridge_independent.py",
            "check_negative_jets_independent.py",
        )]
    report = dict(python=platform.python_version(),
                  evidence="Exact polynomial checks and separate decimal diagnostics; no interval certification.",
                  exact_only=args.exact_only, runs=[])
    log_dir = ROOT / "build" / "verification_logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    for job in jobs:
        started = time.monotonic()
        print("Running " + job[0], flush=True)
        process = subprocess.run([sys.executable, str(ROOT / "verification" / job[0])]
                                 + job[1:], cwd=ROOT, capture_output=True, text=True)
        (log_dir / (Path(job[0]).stem + ".txt")).write_text(
            process.stdout + process.stderr, encoding="utf-8")
        report["runs"].append(dict(script=job[0], returncode=process.returncode,
                                   seconds=round(time.monotonic()-started, 3)))
        (data / "verification_summary.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8")
        if process.returncode:
            print(process.stdout[-3000:] + process.stderr[-3000:], file=sys.stderr)
            raise SystemExit(process.returncode)
        if job[0].startswith("check_"):
            result_names = {
                "check_density_independent.py":"density_independent_checks.json",
                "check_full_scalar_independent.py":"full_scalar_independent_checks.json",
                "check_polylog_bridge_independent.py":"polylog_bridge_independent_checks.json",
                "check_negative_jets_independent.py":"negative_jets_independent_checks.json",
            }
            numerical = json.loads((data / result_names[job[0]]).read_text())
            report["runs"][-1]["residuals_below_1e-40"] = check_residuals(numerical)
    report["status"] = "all selected checks passed"
    (data / "verification_summary.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
