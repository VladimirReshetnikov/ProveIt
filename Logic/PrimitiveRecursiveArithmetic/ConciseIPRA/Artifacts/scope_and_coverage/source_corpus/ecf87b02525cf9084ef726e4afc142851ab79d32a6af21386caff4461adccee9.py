"""Compile the supplied LaTeX report; no network or theorem checker needed."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
if not shutil.which('latexmk') or not shutil.which('pdflatex'):
    raise SystemExit('Install a TeX distribution containing latexmk and pdflatex.')
subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                '-file-line-error', 'report.tex'], cwd=ROOT, check=True)
