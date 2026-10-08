#!/usr/bin/env python3
"""Reproduce checks or measurements without overwriting the recorded evidence.

Usage: python scripts/reproduce.py quick|full|benchmarks
Optional native audit: pip install -r requirements-audit.txt
"""
import argparse
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
FAST = ROOT / "source/Topology/UnknotRecognition/fast"
OUT = ROOT / "reproduction"


def run(name, args, cwd=ROOT):
    OUT.mkdir(exist_ok=True)
    started = time.perf_counter()
    log = OUT / (name + ".log")
    print("Running", name, flush=True)
    with log.open("w", encoding="utf-8") as stream:
        completed = subprocess.run([sys.executable, *map(str, args)], cwd=cwd,
                                   stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.perf_counter() - started
    print("  exit", completed.returncode, "seconds", round(elapsed, 3), flush=True)
    if completed.returncode:
        print("\n".join(log.read_text().splitlines()[-35:]))
        raise SystemExit(completed.returncode)
    return {"name": name, "seconds": elapsed, "exit_code": completed.returncode,
            "log": str(log.relative_to(ROOT))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("quick", "full", "benchmarks"))
    args = parser.parse_args()
    reports = []
    if args.mode == "full" and importlib.util.find_spec("regina") is None:
        parser.error("full audit requires Regina; install requirements-audit.txt or use quick")
    if args.mode == "quick":
        for module in ("affine_modular", "cyclic_cover_family", "normal_interval_extraction",
                       "scalar_inheritance", "primary_split"):
            reports.append(run(module, ["-m", "unittest", "discover", "-s", "tests",
                                         "-p", "test_" + module + ".py", "-v"], FAST))
        reports.append(run("geometry_small", [ROOT / "experiments/geometry/verify_normal_intervals.py",
                           "--skip-regina", "--skip-scaling", "--output", OUT / "geometry_small.json"]))
    if args.mode == "full":
        reports.append(run("full_suite", ["-m", "unittest", "discover", "-s", "tests", "-v"], FAST))
        reports.append(run("geometry_native", [ROOT / "experiments/geometry/verify_normal_intervals.py",
                           "--output", OUT / "geometry_native.json"]))
    if args.mode in ("quick", "full"):
        reports.append(run("family_examples", [ROOT / "scripts/check_family_examples.py",
                           "--report", OUT / "family_example_checks.json"]))
        reports.append(run("peripheral_reduction", [ROOT / "experiments/arithmetic/check_peripheral_reduction.py",
                           "--fast-root", FAST, "--output", OUT / "peripheral_reduction.json"]))
    if args.mode == "benchmarks":
        reports.append(run("arithmetic_benchmarks", [ROOT / "experiments/arithmetic/benchmark_affine_modular.py",
                           "--output", OUT / "affine_modular_benchmarks.json"]))
        reports.append(run("scalar_benchmarks", [FAST / "benchmark_scalar_inheritance.py",
                           "--baseline-file", ROOT / "baseline/Topology/UnknotRecognition/fast/fastunknot/scalar_split.py",
                           "--output", OUT / "scalar_inheritance.json", "--rounds", "7", "--batches", "5"], FAST))
        reports.append(run("normal_scaling", [ROOT / "experiments/geometry/verify_normal_intervals.py",
                           "--skip-regina", "--output", OUT / "normal_scaling.json"]))
    (OUT / (args.mode + "_summary.json")).write_text(json.dumps({
        "mode": args.mode, "python": platform.python_version(), "runs": reports,
        "all_passed": True}, indent=2) + "\n")
    print("All requested checks completed; fresh evidence is in reproduction/.")


if __name__ == "__main__":
    main()
