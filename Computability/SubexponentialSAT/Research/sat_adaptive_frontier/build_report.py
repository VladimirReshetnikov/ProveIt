#!/usr/bin/env python3
"""Compile the complete report with a standard TeX Live installation."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    for iteration in range(3):
        result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                 '-halt-on-error', '-output-directory=' + str(build),
                                 'report.tex'], cwd=ROOT, capture_output=True, text=True)
        (build / ('pass-' + str(iteration + 1) + '.txt')).write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError('LaTeX compilation failed; see build/pass-' + str(iteration + 1) + '.txt')
    log = (build / 'report.log').read_text()
    if 'undefined references' in log or 'undefined citations' in log:
        raise RuntimeError('Unresolved reference; see build/report.log')
    shutil.copy2(build / 'report.pdf', ROOT / 'report.pdf')
    print('Built report.pdf')


if __name__ == '__main__':
    main()
