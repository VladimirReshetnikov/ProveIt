#!/usr/bin/env python3
"""Build the self-contained article, without network access or shell expansion."""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
if shutil.which("latexmk"):
    subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
        cwd=ROOT, check=True,
    )
elif shutil.which("pdflatex"):
    for _ in range(3):
        subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "article.tex"],
            cwd=ROOT, check=True,
        )
else:
    sys.exit("Install TeX Live (including the standard AMS, Latin Modern, and hyperref packages).")
log = (ROOT / "article.log").read_text(errors="replace")
for marker in ("Overfull", "undefined references", "Citation `", "Fatal error"):
    if marker in log:
        sys.exit(f"Build requires review: {marker}")
print(ROOT / "article.pdf")

