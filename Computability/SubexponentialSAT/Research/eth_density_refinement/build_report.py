#!/usr/bin/env python3
"""Rebuild report.pdf using an installed pdflatex; no downloads."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build"

def main():
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdflatex is not installed; install a LaTeX distribution.")
    BUILD.mkdir(exist_ok=True)
    for iteration in range(1, 4):
        with (BUILD / f"pass-{iteration}.stdout").open("w") as log:
            subprocess.run(
                [compiler, "-interaction=nonstopmode", "-halt-on-error",
                 "-output-directory", str(BUILD), str(ROOT / "report.tex")],
                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    shutil.copyfile(BUILD / "report.pdf", ROOT / "report.pdf")
    print("Built report.pdf")

if __name__ == "__main__":
    main()

