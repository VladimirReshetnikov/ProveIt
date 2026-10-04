"""Rebuild the included PDF; requires a local pdflatex installation."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
executable = shutil.which('pdflatex')
if executable is None:
    raise SystemExit('pdflatex is not installed; the already-built PDF remains available.')
for _ in range(3):
    subprocess.run([executable, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                   cwd=root / 'docs', check=True)
print(root / 'docs' / 'report.pdf')
