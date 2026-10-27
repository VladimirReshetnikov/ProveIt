#!/usr/bin/env python3
"""Compile the self-contained report three times, preserving actual compiler errors."""
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent
compiler = shutil.which('pdflatex')
if compiler is None:
    sys.exit('pdflatex was not found; install a TeX distribution first.')
for _ in range(3):
    subprocess.run([compiler, '-interaction=nonstopmode', '-halt-on-error',
                    '3sat_refinement_report.tex'], cwd=root, check=True)
print(root / '3sat_refinement_report.pdf')
