"""Compile report.tex in three passes using an installed pdfLaTeX."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
for _ in range(3):
    run = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                         cwd=ROOT, capture_output=True, text=True)
    if run.returncode:
        print(run.stdout)
        print(run.stderr)
        raise SystemExit(run.returncode)
print(ROOT / 'report.pdf')
