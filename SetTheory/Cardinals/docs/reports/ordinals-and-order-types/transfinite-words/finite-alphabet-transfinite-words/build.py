#!/usr/bin/env python3
"""Cross-platform reproducibility and PDF build driver (Python 3.9+)."""
from __future__ import annotations
import argparse
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-tests", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if not args.skip_tests:
        subprocess.run([sys.executable, str(root / "code" / "verify.py"),
                        "--out", str(root / "data")], cwd=root, check=True)
    build = root / "build"
    build.mkdir(exist_ok=True)
    latexmk = shutil.which("latexmk")
    if latexmk:
        subprocess.run([latexmk, "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                        "-outdir=" + str(build), "article.tex"], cwd=root, check=True)
    else:
        pdflatex = shutil.which("pdflatex")
        if not pdflatex:
            raise SystemExit("No latexmk or pdflatex found. Install a TeX distribution "
                             "with the packages named in article.tex; computations "
                             "can be run independently with code/verify.py.")
        for _ in range(3):
            subprocess.run([pdflatex, "-interaction=nonstopmode", "-halt-on-error",
                            "-output-directory=" + str(build), "article.tex"],
                           cwd=root, check=True)
    pdf = build / "article.pdf"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise SystemExit("The TeX command did not produce a nonempty PDF.")
    shutil.copy2(pdf, root / "article.pdf")
    print("Built:", root / "article.pdf")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as exc:
        raise SystemExit(f"Build step failed with exit status {exc.returncode}.") from exc
