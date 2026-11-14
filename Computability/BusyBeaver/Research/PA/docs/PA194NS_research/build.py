#!/usr/bin/env python3
"""Verify the preserved sources, compile the report, and create a ZIP.
Requires Python 3.10+ and pdflatex on PATH. Does not install dependencies.
This packaging script was used to produce the delivered PDF and ZIP.
"""
from pathlib import Path
import shutil
import os
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
def main():
    if not __debug__:
        raise SystemExit("Do not use -O; the verifier requires assertions.")
    subprocess.run([sys.executable, str(ROOT / "verify.py")], cwd=ROOT, check=True)
    latex = shutil.which("pdflatex")
    if latex is None:
        raise SystemExit("Verification passed. Install a TeX distribution with pdflatex, then rerun build.py; no PDF/ZIP is claimed yet.")
    command = [latex]
    if os.environ.get("PA194_TEX_FORMAT"):
        command.append("-fmt=" + os.environ["PA194_TEX_FORMAT"])
    command += ["-interaction=nonstopmode", "-halt-on-error", "report.tex"]
    for _ in range(2):
        subprocess.run(command, cwd=ROOT, check=True,
            env={**os.environ, "SOURCE_DATE_EPOCH": "1794632870", "FORCE_SOURCE_DATE": "1"})
    pdf = ROOT / "report.pdf"
    if not pdf.is_file() or not pdf.read_bytes().startswith(b"%PDF-"):
        raise SystemExit("PDF output was not produced.")
    target = ROOT.parent / (ROOT.name + ".zip")
    if target.exists():
        raise SystemExit(f"Refusing to replace existing archive: {target}")
    excluded = {".aux", ".log", ".out", ".toc", ".pyc", ".zip"}
    with zipfile.ZipFile(target, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for file in sorted(ROOT.rglob("*")):
            if file.is_file() and file.suffix not in excluded and "__pycache__" not in file.parts:
                archive.write(file, ROOT.name + "/" + file.relative_to(ROOT).as_posix())
    print(f"Created {target}")
    print("Inspect report.pdf visually before treating it as publication-ready.")
if __name__ == "__main__":
    main()
