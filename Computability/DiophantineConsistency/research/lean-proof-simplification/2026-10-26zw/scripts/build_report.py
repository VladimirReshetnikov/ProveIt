#!/usr/bin/env python3
"""Build the LaTeX article, resolving cross-references with a second pass."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
for _ in range(2):
    proc = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                           '-halt-on-error', 'report.tex'], cwd=root,
                          text=True, capture_output=True)
    if proc.returncode:
        print(proc.stdout + proc.stderr)
        raise SystemExit(proc.returncode)
print(root / 'report.pdf')
