"""Compile the complete paper; no network access is used."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
for _ in range(2):
    subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                    'report.tex'], cwd=root, check=True)
