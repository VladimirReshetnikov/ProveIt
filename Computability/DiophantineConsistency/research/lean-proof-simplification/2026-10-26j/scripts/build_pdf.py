#!/usr/bin/env python3
"""Build report.pdf from report.tex with pdflatex; fail on either pass."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
for iteration in (1, 2):
    p = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                        'report.tex'], cwd=root, text=True, capture_output=True)
    (root / 'evidence' / f'latex-pass{iteration}.log').write_text(
        p.stdout + p.stderr, encoding='utf-8')
    if p.returncode:
        raise SystemExit(p.returncode)
print(root / 'report.pdf')
