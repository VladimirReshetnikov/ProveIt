#!/usr/bin/env python3
"""Compile every supplied article twice with a normally configured pdflatex."""
from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent
for tex in [root/'report.tex',*sorted((root/'notes').glob('*.tex'))]:
    for _ in range(2):
        subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(tex.parent),str(tex)],cwd=root,check=True)
