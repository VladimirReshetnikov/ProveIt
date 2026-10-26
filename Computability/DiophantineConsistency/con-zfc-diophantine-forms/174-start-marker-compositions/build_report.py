#!/usr/bin/env python3
"""Check printed data and compile report.tex with a standard TeX installation.

Run from any directory.  Requires pdflatex and the packages declared in
report.tex; no network operation or package installation is performed.
The PDF is written to report.pdf.  PDF bytes can depend on the TeX version.
"""
from pathlib import Path
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    compiler = shutil.which('pdflatex')
    if compiler is None:
        raise SystemExit('pdflatex is required; install a TeX distribution before rebuilding the report.')
    subprocess.run([sys.executable, '-B', str(ROOT / 'build_appendices.py'), '--check'], check=True)
    environment = os.environ.copy()
    environment.setdefault('SOURCE_DATE_EPOCH', '1792886400')
    environment.setdefault('FORCE_SOURCE_DATE', '1')
    for number in range(3):
        result = subprocess.run(
            [compiler, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
            cwd=ROOT, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
    log = (ROOT / 'report.log').read_text(errors='replace')
    problems = [line for line in log.splitlines()
                if 'Overfull' in line or 'undefined' in line or 'Rerun to get' in line]
    if problems:
        raise SystemExit('Resolve these TeX diagnostics:\n' + '\n'.join(problems))
    print('PASS: report.pdf compiled in three passes without overflow or unresolved references.')


if __name__ == '__main__':
    main()
