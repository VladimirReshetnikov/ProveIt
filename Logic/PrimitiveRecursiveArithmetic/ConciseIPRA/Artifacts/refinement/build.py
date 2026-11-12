"""Compile the complete LaTeX report twice, without runtime downloads."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
if shutil.which("pdflatex") is None:
    raise SystemExit("pdflatex is required to compile report.tex")
for _ in range(2):
    result = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "report.tex"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        raise SystemExit(result.stdout.decode("utf-8", errors="replace"))
print(root / "report.pdf")
