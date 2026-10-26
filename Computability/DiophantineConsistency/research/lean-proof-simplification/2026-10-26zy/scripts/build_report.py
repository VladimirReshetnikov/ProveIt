#!/usr/bin/env python3
"""Build the report with XeLaTeX; no external bibliography step is needed."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
for _ in range(2):
    subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error',
                    '-file-line-error', 'report.tex'], cwd=ROOT, check=True)
print(ROOT / 'report.pdf')
