#!/usr/bin/env python3
"""Build the standalone article, optionally rerunning all exact checks.

With --check this runs the ten unit tests and then all three verifiers:
code/verify.py, code/verify_transfer.py and code/verify_supportwise.py.
"""
import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Run full exact checks first.")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    try:
        if args.check:
            subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "code"],
                           cwd=root, check=True)
            subprocess.run([sys.executable, "code/verify.py"], cwd=root, check=True)
            subprocess.run([sys.executable, "code/verify_transfer.py"],
                           cwd=root, check=True)
            subprocess.run([sys.executable, "code/verify_supportwise.py"],
                           cwd=root, check=True)
        if shutil.which("latexmk"):
            commands = [["latexmk", "-pdf", "-interaction=nonstopmode",
                         "-halt-on-error", "article.tex"]]
        elif shutil.which("pdflatex"):
            commands = [["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                         "article.tex"]] * 2
        else:
            print("No latexmk or pdflatex found. The archive includes a prebuilt article.pdf.",
                  file=sys.stderr)
            return 2
        for command in commands:
            subprocess.run(command, cwd=root, check=True)
        print(root / "article.pdf")
        return 0
    except subprocess.CalledProcessError as error:
        print(f"Build/check command failed with exit code {error.returncode}.", file=sys.stderr)
        return error.returncode or 1


if __name__ == "__main__":
    raise SystemExit(main())
