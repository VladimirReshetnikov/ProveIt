#!/usr/bin/env python3
"""Run the primary PA194ZR checks; discovery searches are never required."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="Omit both full symbolic contract passes.")
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O: assertions are certificate checks.")
    checks = [
        ["build_verify.py"] + (["--quick"] if args.quick else []),
        ["verification/check_source_equivalence.py",
         "--original", "reference/parentCS/machine/pa194CS.instructions.json",
         "--modified", "source/instructions.json",
         "--output", "proof/independent_source_invariant.json"],
        ["verification/check_startup.py",
         "--table", "machine/pa194zr.native.tm",
         "--sites", "source/sites.json",
         "--output", "proof/second_startup_receipt.json"],
        ["comparison/check_novelty.py",
         "--candidate", "machine/pa194zr.tm", "--start", "0",
         "--census", "comparison/census_current/census.json",
         "--table-dir", "comparison/census_current/tables",
         "--output", "comparison/novelty_replayed.json"],
    ]
    if not args.quick:
        checks.insert(2, ["verification/check_literal.py"])
    for command in checks:
        print("\nRunning " + " ".join(command), flush=True)
        subprocess.run([sys.executable, "-B"] + command, cwd=ROOT, check=True)
    print("\nAll requested PA194ZR checks passed.", flush=True)


if __name__ == "__main__":
    main()
