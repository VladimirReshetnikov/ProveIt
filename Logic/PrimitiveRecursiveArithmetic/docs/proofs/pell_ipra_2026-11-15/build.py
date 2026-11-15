#!/usr/bin/env python3
"""Rebuild the article PDF; requires pdflatex and the listed TeX packages."""

from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
build = root / "build"
build.mkdir(exist_ok=True)
engine = shutil.which("pdflatex")
if engine is None:
    raise SystemExit("pdflatex is required; install a standard TeX Live distribution")
command = [engine, "-interaction=nonstopmode", "-halt-on-error",
           "-file-line-error", "-output-directory", str(build),
           str(root / "pell_ipra.tex")]
for pass_number in range(3):
    completed = subprocess.run(command, cwd=root, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (build / f"pdflatex-pass-{pass_number + 1}.txt").write_text(
        completed.stdout, encoding="utf-8")
    if completed.returncode:
        print(completed.stdout[-12000:])
        raise SystemExit(completed.returncode)
shutil.copy2(build / "pell_ipra.pdf", root / "pell_ipra.pdf")
print(f"Built {root / 'pell_ipra.pdf'}")

