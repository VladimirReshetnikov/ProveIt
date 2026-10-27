#!/usr/bin/env python3
"""Build the LaTeX report; requires pdflatex and standard TeX packages."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
if shutil.which("pdflatex") is None:
    raise SystemExit("Install TeX Live or another distribution providing pdflatex.")
for _ in range(2):
    subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                    "-file-line-error", "report.tex"],
                   cwd=ROOT / "report", check=True)
print(ROOT / "report" / "report.pdf")
