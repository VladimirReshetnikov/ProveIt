#!/usr/bin/env python3
"""Build the complete report offline with shell escape disabled."""
from pathlib import Path
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
BUILD=ROOT/'_build'
BUILD.mkdir(exist_ok=True)
for _ in range(2):
    result=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                           '-halt-on-error','-output-directory='+str(BUILD),
                           'report.tex'],cwd=ROOT,capture_output=True,text=True)
    if result.returncode:
        print(result.stdout[-12000:])
        raise SystemExit(result.returncode)
shutil.copy2(BUILD/'report.pdf',ROOT/'report.pdf')
print('Built report.pdf; compilation log is in _build/report.log')
