#!/usr/bin/env python3
"""Rebuild checks, figure, and PDF in a standard Python/TeX environment."""
from pathlib import Path
import shutil
import subprocess
import sys

root=Path(__file__).resolve().parents[1]
for script in ['verify_resonance.py','verify_characters.py','make_figures.py']:
    subprocess.run([sys.executable,str(root/'code'/script)],cwd=root,check=True)
build=root/'build'
build.mkdir(exist_ok=True)
if shutil.which('pdflatex'):
    command=['pdflatex','-interaction=nonstopmode','-halt-on-error',
             '-output-directory',str(build),'main.tex']
    for _ in range(2):
        subprocess.run(command,cwd=root,check=True)
elif shutil.which('tectonic'):
    subprocess.run(['tectonic','main.tex','--outdir',str(build)],cwd=root,check=True)
else:
    raise SystemExit('Install a working TeX distribution (pdflatex or Tectonic).')
shutil.copy2(build/'main.pdf',root/'grh_prime_resonance.pdf')
print('Rebuilt grh_prime_resonance.pdf')
