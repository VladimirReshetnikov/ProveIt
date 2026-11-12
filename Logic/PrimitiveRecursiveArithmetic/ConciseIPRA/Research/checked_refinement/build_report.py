"""Compile the complete report using a normal TeX Live installation."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
for _ in range(3):
    subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
        cwd=root,
        check=True,
    )
print(root / "report.pdf")
