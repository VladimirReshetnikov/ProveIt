#!/usr/bin/env python3
"""Build the standalone report in a temporary LaTeX directory."""
from pathlib import Path
import argparse
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', type=Path, default=root / 'report.pdf')
parser.add_argument('--pdflatex', default='pdflatex')
args = parser.parse_args()
destination = args.out.resolve()
destination.parent.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(prefix='k215-report-') as tmp:
    work = Path(tmp)
    shutil.copyfile(root / 'report.tex', work / 'report.tex')
    for pass_number in range(1, 3):
        result = subprocess.run(
            [args.pdflatex, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
            cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
    log = (work / 'report.log').read_text(errors='replace')
    if 'Overfull ' in log or 'undefined references' in log:
        print(log)
        raise SystemExit('Document check failed: overflow or unresolved references.')
    shutil.copyfile(work / 'report.pdf', destination)
print('Built', destination)
