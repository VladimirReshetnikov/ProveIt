"""Compile the complete LaTeX report."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
engine = shutil.which("pdflatex")
if engine is None:
    raise SystemExit("pdflatex is required to build report.pdf")
for _ in range(2):
    subprocess.run([engine, "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
                   cwd=root, check=True)
print(root / "report.pdf")
