#!/usr/bin/env python3
"""Rebuild the report using a local pdflatex installation, with no network."""
from pathlib import Path
import subprocess
root = Path(__file__).resolve().parents[1]
for _ in range(2):
    subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','report.tex'],cwd=root,check=True)
print(root/'report.pdf')
