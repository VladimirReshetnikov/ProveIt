#!/usr/bin/env python3
"""Run the included exact and high-precision checks sequentially."""
from pathlib import Path
import argparse
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
EXACT = ["verify_ranks.py", "verify_jet_ranks.py",
         "verify_shuffle_audit.py", "verify_cubic_class_numbers.py"]
NUMERICAL = ["verify_bridge.py", "verify_gaussian.py", "verify_corrections.py",
             "verify_polylog_corrections.py", "verify_stieltjes_zeros.py"]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-only", action="store_true",
                        help="Run the four finite exact-arithmetic programs only.")
    args = parser.parse_args()
    start = time.monotonic()
    for name in EXACT + ([] if args.exact_only else NUMERICAL):
        print(f"\nRunning {name}", flush=True)
        subprocess.run([sys.executable, str(HERE / name)], check=True)
    print(f"\nAll selected programs passed in {time.monotonic()-start:.1f} seconds.")

if __name__ == "__main__":
    main()
