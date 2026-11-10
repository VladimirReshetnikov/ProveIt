"""Build the complete LaTeX report; no network or shell escape."""
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parent
for _ in range(3):
    result=subprocess.run(["pdflatex","-interaction=nonstopmode","-halt-on-error",
                           "-no-shell-escape","report.tex"],cwd=ROOT,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if result.returncode:
        print(result.stdout[-8000:])
        raise SystemExit(result.returncode)
print("Built report.pdf")
