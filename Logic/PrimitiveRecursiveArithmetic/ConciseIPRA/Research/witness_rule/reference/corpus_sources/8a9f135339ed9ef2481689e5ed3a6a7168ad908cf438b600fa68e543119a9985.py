"""Compile the report from its included LaTeX sources."""
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
build = ROOT / 'tmp' / 'latex'
build.mkdir(parents=True, exist_ok=True)
for _ in range(3):
    result = subprocess.run([
        'pdflatex', '-output-format=pdf', '-interaction=nonstopmode', '-halt-on-error',
        '-file-line-error', '-output-directory=' + str(build), 'report.tex'
    ], cwd=ROOT, capture_output=True, text=True)
    (build / 'last-build.txt').write_text(result.stdout + result.stderr)
    if result.returncode:
        print((result.stdout + result.stderr)[-12000:])
        raise SystemExit(result.returncode)
shutil.copyfile(build / 'report.pdf', ROOT / 'report.pdf')
print('Created report.pdf')
