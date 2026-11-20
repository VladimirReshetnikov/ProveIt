"""Reproduce the exact arithmetic checks and optionally the Lean and PDF builds.

Usage: python3 reproduce.py [--lean] [--pdf]
Only the Python standard library is needed for the default arithmetic checks.
External tools are required only for the explicitly selected optional stages.
"""
from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="also compile and validate the Lean project")
    parser.add_argument("--pdf", action="store_true", help="also rebuild the report with pdfLaTeX")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    subprocess.run([sys.executable, str(root / "code" / "verify.py")], check=True)
    if args.lean:
        lake = shutil.which("lake")
        if lake is None:
            raise SystemExit("Lean stage needs Lean 4.19.0 and lake on PATH.")
        subprocess.run([lake, "build"], cwd=root / "lean", check=True)
        subprocess.run([lake, "env", "lean", "Validation.lean"], cwd=root / "lean", check=True)
    if args.pdf:
        subprocess.run([sys.executable, str(root / "build_pdf.py")], check=True)


if __name__ == "__main__":
    main()
