"""Compile the LaTeX report; requires pdflatex and ordinary TeX packages."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
if not shutil.which('pdflatex'):
    raise SystemExit('Install a TeX distribution providing pdflatex to rebuild report.pdf.')
for _ in range(3):
    process = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                             cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if process.returncode:
        print('\n'.join(process.stdout.splitlines()[-50:]))
        raise SystemExit(process.returncode)
print(root / 'report.pdf')
