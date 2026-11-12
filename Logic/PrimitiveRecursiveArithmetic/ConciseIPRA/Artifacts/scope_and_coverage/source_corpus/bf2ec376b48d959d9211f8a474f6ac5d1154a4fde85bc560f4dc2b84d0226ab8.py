"""Compile the complete report using pdfLaTeX, with shell escape disabled."""
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent
for _ in range(3):
    subprocess.run([
        "pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
        "-halt-on-error", "report.tex"
    ], cwd=root, check=True)
print(root / "report.pdf")
