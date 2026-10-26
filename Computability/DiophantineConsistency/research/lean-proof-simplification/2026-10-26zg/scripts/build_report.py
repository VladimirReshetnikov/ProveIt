#!/usr/bin/env python3
"""Build the PDF with a local XeLaTeX installation; installs nothing."""
from pathlib import Path
import shutil
import subprocess

report = Path(__file__).resolve().parents[1] / "report"
compiler = shutil.which("xelatex")
if compiler is None:
    raise SystemExit("XeLaTeX is required; see README.txt for fonts and packages.")
# Three passes stabilize the contents and page references after a fresh build.
for _ in range(3):
    subprocess.run([compiler, "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
                   cwd=report, check=True)
print(report / "report.pdf")
