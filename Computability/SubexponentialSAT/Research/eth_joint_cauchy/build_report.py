#!/usr/bin/env python3
"""Compile report.tex with shell escape disabled; keep auxiliary files separate."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
build = root / "_build"
build.mkdir(exist_ok=True)
if not shutil.which("pdflatex"):
    raise SystemExit("pdflatex is required; install a standard LaTeX distribution.")
for iteration in range(1, 4):
    result = subprocess.run(
        ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
         "-file-line-error", "-output-directory", str(build), "report.tex"],
        cwd=root, capture_output=True, text=True, check=False)
    (build / f"pass_{iteration}.txt").write_text(result.stdout + result.stderr, encoding="utf-8")
    if result.returncode:
        print(result.stdout[-10000:])
        raise SystemExit(f"LaTeX failed on pass {iteration}; see _build/pass_{iteration}.txt")
    log = (build / "report.log").read_text(encoding="utf-8", errors="replace")
    if iteration >= 2 and "Rerun to get cross-references right" not in log:
        break
if "There were undefined references" in log or "Citation `" in log and "undefined" in log:
    raise SystemExit("The report still has unresolved references; inspect _build/report.log")
shutil.copyfile(build / "report.pdf", root / "report.pdf")
print(root / "report.pdf")
