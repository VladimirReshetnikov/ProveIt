#!/usr/bin/env python3
"""Compile report.tex to report.pdf, retaining LaTeX intermediates in build/."""
from pathlib import Path
import shutil
import subprocess


def main() -> None:
    root = Path(__file__).resolve().parent
    compiler = shutil.which("pdflatex")
    if compiler is None:
        raise SystemExit("pdflatex is required (a normal TeX Live or MiKTeX installation).")
    build = root / "build"
    build.mkdir(exist_ok=True)
    for _ in range(3):
        run = subprocess.run(
            [compiler, "-interaction=nonstopmode", "-halt-on-error",
             "-output-directory", str(build), "report.tex"],
            cwd=root, capture_output=True, text=True)
        (build / "last-compile-output.txt").write_text(run.stdout + run.stderr)
        if run.returncode:
            print(run.stdout)
            print(run.stderr)
            raise SystemExit(run.returncode)
    shutil.copy2(build / "report.pdf", root / "report.pdf")
    print(root / "report.pdf")


if __name__ == "__main__":
    main()
