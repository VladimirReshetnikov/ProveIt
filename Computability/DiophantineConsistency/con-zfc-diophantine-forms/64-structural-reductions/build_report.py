#!/usr/bin/env python3
"""Build the supplied article with two pdflatex passes (TeX Live required)."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent

if shutil.which('pdflatex') is None:
    raise SystemExit('pdflatex is required; install a normal TeX Live distribution.')

for pass_number in range(2):
    process = subprocess.run(
        ['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
        cwd=ROOT / 'report', text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if process.returncode:
        raise SystemExit(process.stdout)

log = (ROOT / 'report/report.log').read_text(errors='replace')
warnings = [line for line in log.splitlines()
            if 'Overfull' in line or 'undefined' in line or 'LaTeX Warning:' in line]
print('Built report/report.pdf')
for warning in warnings:
    print(warning)
