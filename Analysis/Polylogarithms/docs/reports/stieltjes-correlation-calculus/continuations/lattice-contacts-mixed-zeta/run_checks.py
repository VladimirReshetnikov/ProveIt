#!/usr/bin/env python3
"""Replay the six independent verification programs."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    "verify_mixed_tails.py",
    "check_lattice_contacts.py",
    "check_mixed_tails_numeric.py",
    "check_modular_transport.py",
    "verify_independent_shifts.py",
    "verify_spectral_faces.py",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact-mixed-only", action="store_true",
                        help="Run only the standard-library exact mixed-tail certificates.")
    args = parser.parse_args()
    selected = PROGRAMS[:1] if args.exact_mixed_only else PROGRAMS
    (ROOT / "results").mkdir(exist_ok=True)
    for name in selected:
        print(f"Running {name}", flush=True)
        subprocess.run([sys.executable, str(ROOT / "verification" / name)], cwd=ROOT, check=True)
    print("All selected programs passed.")


if __name__ == "__main__":
    main()

