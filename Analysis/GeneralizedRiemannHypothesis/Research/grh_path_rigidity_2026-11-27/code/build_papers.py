#!/usr/bin/env python3
"""Rebuild both PDFs with a standard pdflatex installation."""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parents[1]
for name in ['pathwise_rigidity','sharp_extremal_results']:
    for _ in range(2):
        subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',name+'.tex'],
                       cwd=root/'papers',check=True)
    print(root/'papers'/(name+'.pdf'))
