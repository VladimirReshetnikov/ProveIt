"""Compile the complete report; no shell escape is used."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
for _ in range(3):
    result = subprocess.run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
                             "-halt-on-error", "report.tex"], cwd=root,
                            text=True, capture_output=True)
    if result.returncode:
        print(result.stdout[-8000:])
        raise SystemExit(result.returncode)
print(root / "report.pdf")
