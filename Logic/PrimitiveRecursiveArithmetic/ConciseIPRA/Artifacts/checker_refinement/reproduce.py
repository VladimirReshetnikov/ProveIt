"""Reproduce the checker comparisons and optionally rebuild the report."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf", action="store_true")
    options = parser.parse_args()
    subprocess.run([sys.executable, "verify.py"], cwd=ROOT, check=True)
    if options.pdf:
        subprocess.run([sys.executable, "build_pdf.py"], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
