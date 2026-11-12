#!/usr/bin/env python3
"""Build the report with a normal installed pdfLaTeX distribution."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    executable = shutil.which('pdflatex')
    if not executable:
        raise SystemExit('Install pdfLaTeX with the packages named in the source.')
    command = [executable, '-interaction=nonstopmode', '-halt-on-error',
               'ipra_parameter_witness.tex']
    for _ in range(3):
        subprocess.run(command, cwd=ROOT, check=True)
    print(ROOT / 'ipra_parameter_witness.pdf')


if __name__ == '__main__':
    main()
