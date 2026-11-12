#!/usr/bin/env python3
"""Compile the supplied LaTeX paper twice with a standard TeX installation."""
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent
engine = shutil.which('pdflatex')
if engine is None:
    sys.exit('pdflatex is required; install a standard TeX Live distribution.')
for run in range(2):
    subprocess.run(
        [engine, '-interaction=nonstopmode', '-halt-on-error', 'ipra_one_body.tex'],
        cwd=root, check=True,
    )
print(root / 'ipra_one_body.pdf')
