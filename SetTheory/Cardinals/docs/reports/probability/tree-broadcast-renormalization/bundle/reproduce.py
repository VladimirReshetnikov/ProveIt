#!/usr/bin/env python3
"""Reproduce the delivered exact checks and/or compile the three articles."""
from __future__ import annotations
import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PAPERS = (
    "01_universal_avoidance",
    "02_parabolic_amplitudes",
    "03_tree_broadcast",
)

def run(command: list[str], directory: str) -> None:
    print(f"\n[{directory}] {' '.join(command)}", flush=True)
    subprocess.run(command, cwd=ROOT / directory, check=True)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks", action="store_true", help="run all exact finite checks")
    parser.add_argument("--pdfs", action="store_true", help="compile all three article PDFs")
    args = parser.parse_args()
    if not (args.checks or args.pdfs):
        parser.error("choose --checks, --pdfs, or both")
    if args.checks:
        run([sys.executable, "code/verify_exact.py", "--output",
             "data/verification_results.json"], PAPERS[0])
        run([sys.executable, "code/verify_exact.py", "--output",
             "data/exact_checks.json"], PAPERS[1])
        run([sys.executable, "verify.py", "--output",
             "verification.json"], PAPERS[2])
    if args.pdfs:
        for directory in PAPERS:
            run(["latexmk", "-pdf", "-interaction=nonstopmode",
                 "-halt-on-error", "article.tex"], directory)
    print("\nRequested reproduction steps completed.", flush=True)

if __name__ == "__main__":
    main()
