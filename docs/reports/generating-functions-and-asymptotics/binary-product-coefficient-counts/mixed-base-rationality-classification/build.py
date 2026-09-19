#!/usr/bin/env python3
"""Rebuild article.pdf from bundled sources; standard library only.

Usage: python build.py [--verify]
A working pdfLaTeX installation is required. Figures are already included.
"""
import argparse
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true",
                        help="run exact finite verification before building")
    args = parser.parse_args()
    latex = shutil.which("pdflatex")
    if latex is None:
        print("pdfLaTeX was not found on PATH. The prebuilt article.pdf is included.",
              file=sys.stderr)
        return 1
    for name in ("coefficient_profile.pdf", "normalized_counts.pdf"):
        if not (ROOT / "figures" / name).is_file():
            print(f"Missing bundled figure: figures/{name}", file=sys.stderr)
            return 1
    try:
        if args.verify:
            subprocess.run([sys.executable, str(ROOT / "code" / "verify.py")],
                           cwd=ROOT, check=True)
        command = [latex, "-interaction=nonstopmode", "-halt-on-error", "article.tex"]
        for _ in range(2):
            subprocess.run(command, cwd=ROOT, check=True)
    except subprocess.CalledProcessError as error:
        print(f"Build stopped with exit code {error.returncode}.", file=sys.stderr)
        return error.returncode or 1
    print(f"Built {ROOT / 'article.pdf'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
