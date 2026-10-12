#!/usr/bin/env python3
"""Run the bundled checks or reproduce a selected research experiment."""
import argparse
import json
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FAST = ROOT / "integration" / "native_snapshot"


def run(arguments, log_path):
    command = [sys.executable, "-B", *map(str, arguments)]
    print("$ " + shlex.join(command), flush=True)
    with log_path.open("w") as log:
        result = subprocess.run(command, cwd=ROOT, text=True,
                                stdout=log, stderr=subprocess.STDOUT)
    print(log_path.read_text(), end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--synthetic", action="store_true",
                        help="repeat complete weighted-verifier comparisons")
    parser.add_argument("--native", action="store_true",
                        help="repeat all 11 native whole-query comparisons")
    parser.add_argument("--chamber-audit", action="store_true",
                        help="repeat the 106-case audit and connected binary stress")
    parser.add_argument("--rounds", type=int, default=3,
                        help="paired benchmark repetitions (default: 3)")
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    output = ROOT / "reproduced"
    output.mkdir(exist_ok=True)
    if not any((args.synthetic, args.native, args.chamber_audit)):
        run([ROOT / "integration" / "verify_integration.py", "--new-tests"],
            output / "new_tests.log")
        run([ROOT / "scripts" / "validate_chamber_examples.py",
             "--fast-root", FAST,
             ROOT / "examples" / "three_parallel_meridians.json",
             ROOT / "examples" / "exponential_meridian_128.json"],
            output / "stored_packets.log")
        (output / "checks.json").write_text(json.dumps({
            "status": "PASS",
            "new_test_methods": 18,
            "stored_source_packets": 2,
            "python": sys.version,
        }, indent=2) + "\n")
    if args.synthetic:
        run([ROOT / "scripts" / "benchmark_rope.py", "--fast", FAST,
             "--synthetic", "--rounds", args.rounds,
             "--output", output / "synthetic_benchmark.json"],
            output / "synthetic_benchmark.log")
    if args.native:
        run([ROOT / "scripts" / "benchmark_rope.py", "--fast", FAST,
             "--baseline-verifier", ROOT / "integration" / "reference" /
             "weighted_orbit_verify_baseline.py",
             "--cases", ROOT / "results" / "native_cases.json",
             "--rounds", args.rounds,
             "--output", output / "native_benchmark.json"],
            output / "native_benchmark.log")
    if args.chamber_audit:
        run([ROOT / "scripts" / "chamber_graph_audit.py",
             "--fast-root", FAST,
             "--output", output / "chamber_graph_audit.json"],
            output / "chamber_graph_audit.log")
    print("Requested reproduction completed. Original observations are unchanged.",
          flush=True)


if __name__ == "__main__":
    main()
