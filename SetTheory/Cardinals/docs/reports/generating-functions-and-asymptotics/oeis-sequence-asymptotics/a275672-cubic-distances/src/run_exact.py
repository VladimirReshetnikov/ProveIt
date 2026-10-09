#!/usr/bin/env python3
"""Validated entry point for the frozen A275672 exhaustive-search sources.

Examples:
  python3 src/run_exact.py 8 13 --seconds 3600 --mode top6
  python3 src/run_exact.py 9 14 --variant prefix-filtered --seconds 3600

The C++ programs emit JSON to stdout and case records to stderr. A timeout
remains UNKNOWN. A single --case run never covers the other diameter cases.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("target", type=int)
    parser.add_argument("--seconds", type=float, default=600)
    parser.add_argument("--mode", choices=["diameters"] +
                        [f"top{i}" for i in range(2, 7)], default="top6")
    parser.add_argument("--variant", choices=["frozen", "prefix-filtered"],
                        default="frozen")
    parser.add_argument("--case", type=int, dest="case_index")
    parser.add_argument("--compiler", default="g++")
    args = parser.parse_args()
    if not 1 <= args.n <= 10:
        parser.error("The fixed-mask search supports side lengths 1 through 10.")
    if args.target < 1:
        parser.error("The target must be a positive integer.")
    if not math.isfinite(args.seconds) or args.seconds <= 0:
        parser.error("The time budget must be positive and finite.")
    vertices = args.n**3
    if args.case_index is not None and not (
            0 <= args.case_index < vertices*(vertices-1)//2):
        parser.error("Case index is outside the possible unordered-edge range.")
    # Resolve huge targets before passing them to the unchanged C++ sources.
    # Their signed-int pair count is safe for target <= n^3 <= 1000.
    if args.target > vertices:
        print(json.dumps({"n":args.n, "target":args.target, "status":"UNSAT",
                          "scope":"global_vertex_count", "nodes":0}))
        return 0
    if args.target <= 2:
        points = [[0,0,0]]
        if args.target == 2:
            points.append([args.n-1,0,0])
        print(json.dumps({"n":args.n, "target":args.target, "status":"SAT",
                          "scope":"explicit_trivial_witness", "points":points}))
        return 0
    if args.variant == "prefix-filtered":
        source = ROOT/"computations/exploratory/rainbow_prefix_filtered.cpp"
    elif args.mode == "diameters":
        source = ROOT/"computations/exact/rainbow_exact_v5.cpp"
    else:
        source = ROOT/"computations/exact/rainbow_edge_prefix.cpp"
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    build = ROOT/"build"
    build.mkdir(exist_ok=True)
    executable = build/f"{source.stem}_{digest[:16]}"
    if not executable.is_file():
        subprocess.run([args.compiler, "-O3", "-std=c++17", str(source),
                        "-o", str(executable)], check=True)
    command = [str(executable), str(args.n), str(args.target),
               str(args.seconds), args.mode]
    if args.case_index is not None:
        command.append(str(args.case_index))
    print(f"Source: {source.relative_to(ROOT)}; SHA-256: {digest}", file=sys.stderr)
    return subprocess.run(command).returncode


if __name__ == "__main__":
    raise SystemExit(main())
