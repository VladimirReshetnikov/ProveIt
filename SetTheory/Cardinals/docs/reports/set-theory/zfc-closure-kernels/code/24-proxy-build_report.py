#!/usr/bin/env python3
"""Build report.pdf from the included source with a normal LaTeX install."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
if not shutil.which("pdflatex"):
    raise SystemExit("pdflatex is required. Install a normal LaTeX distribution first.")
build = root / "tmp" / "pdf"
build.mkdir(parents=True, exist_ok=True)
for _ in range(3):
    subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                    "-file-line-error", "-output-directory", str(build),
                    "report.tex"], cwd=root, check=True)
shutil.copy2(build / "report.pdf", root / "report.pdf")
print(root / "report.pdf")
