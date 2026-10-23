#!/usr/bin/env python3
"""Compile the article; Python standard library and pdflatex are required."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
engine = shutil.which('pdflatex')
if not engine:
    raise SystemExit('pdflatex is required to rebuild report.pdf')
for number in range(1, 4):
    result = subprocess.run(
        [engine, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    print('LaTeX pass', number, 'completed')
print('Created', ROOT/'report.pdf')
