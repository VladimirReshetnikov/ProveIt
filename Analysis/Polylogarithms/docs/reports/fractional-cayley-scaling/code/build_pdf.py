#!/usr/bin/env python3
"""Build article.pdf without latexmk, with three reference-resolution passes."""
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parents[1]
for attempt in range(3):
    subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error","-file-line-error","article.tex"],cwd=root,check=True)
print(root/"article.pdf")
