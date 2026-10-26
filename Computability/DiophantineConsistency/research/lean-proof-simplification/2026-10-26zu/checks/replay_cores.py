#!/usr/bin/env python3
"""Replay the two exact delivered standard-library checkers with Lean 4.32.0."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

PACKET = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.32.0 executable")
    args = parser.parse_args()
    version = subprocess.run([args.lean, "--version"], text=True,
                             capture_output=True, check=True).stdout.strip()
    if "version 4.32.0" not in version:
        raise SystemExit(f"Expected Lean 4.32.0; found {version}")
    print(version, flush=True)
    results = []
    for relative in ["shape/ShapeCore.lean", "growth/FullExponentGrowth.lean"]:
        print(f"Checking {relative}", flush=True)
        result = subprocess.run([args.lean, str(PACKET / relative)], cwd=PACKET)
        results.append({"source": relative, "exit_code": result.returncode})
        if result.returncode:
            print(json.dumps(results, indent=2))
            return result.returncode
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
