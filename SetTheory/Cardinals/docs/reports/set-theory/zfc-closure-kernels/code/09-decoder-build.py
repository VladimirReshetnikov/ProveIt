#!/usr/bin/env python3
"""Build the complete report with pdflatex; no network or BibTeX needed."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    binary = shutil.which('pdflatex')
    if binary is None:
        raise SystemExit('pdflatex is required. Install a TeX distribution and try again.')
    for _ in range(3):
        run = subprocess.run([binary, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                             cwd=ROOT/'article', text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, errors='replace')
        if run.returncode:
            print(run.stdout)
            raise SystemExit(run.returncode)
    log = (ROOT/'article/report.log').read_text(errors='replace')
    problems = [line for line in log.splitlines()
                if 'Overfull' in line or 'undefined' in line.lower()]
    if problems:
        print('\n'.join(problems))
        raise SystemExit('The PDF built, but layout/reference warnings need review.')
    print('Built article/report.pdf. The supplied integrity manifest was not changed.')


if __name__ == '__main__':
    main()
