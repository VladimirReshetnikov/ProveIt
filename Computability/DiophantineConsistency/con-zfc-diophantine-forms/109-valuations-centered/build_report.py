#!/usr/bin/env python3
"""Compile the complete report twice; require clean references and no overflow."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
for _ in range(2):
    result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                             '-halt-on-error', 'report.tex'],
                            cwd=ROOT / 'report', text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
log = (ROOT / 'report/report.log').read_text()
for marker in ['Overfull \\hbox', 'Overfull \\vbox',
               'There were undefined references', 'undefined on input line']:
    if marker in log:
        raise SystemExit('Layout/reference check failed: ' + marker)
print('Compiled report/report.pdf with clean references and no overfull boxes.')
