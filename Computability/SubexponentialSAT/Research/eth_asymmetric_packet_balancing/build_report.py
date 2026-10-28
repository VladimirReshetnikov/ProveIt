#!/usr/bin/env python3
"""Rebuild the complete report using local pdfLaTeX, with no shell escape."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
build = root / 'build'
build.mkdir(exist_ok=True)
engine = shutil.which('pdflatex')
if engine is None:
    raise SystemExit('Install pdfLaTeX and the standard packages listed in README.txt.')
for i in range(1, 4):
    log = build / f'pass{i}.stdout'
    with log.open('w', encoding='utf-8') as stream:
        result = subprocess.run([engine, '-no-shell-escape', '-interaction=nonstopmode',
                                 '-halt-on-error', '-output-directory=' + str(build),
                                 'report.tex'], cwd=root, stdout=stream,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f'pdfLaTeX failed; inspect {log}')
final_log = (build / 'report.log').read_text(errors='replace')
if 'undefined references' in final_log or 'undefined citations' in final_log:
    raise SystemExit('Unresolved references remain; inspect build/report.log.')
shutil.copyfile(build / 'report.pdf', root / 'report.pdf')
print(root / 'report.pdf')
