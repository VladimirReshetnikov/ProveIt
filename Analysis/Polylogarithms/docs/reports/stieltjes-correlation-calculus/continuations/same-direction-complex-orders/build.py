#!/usr/bin/env python3
"""Compile the article with three serial passes; requires a TeX installation.

Usage: python build.py [--engine pdflatex|lualatex]
Intermediate files remain in build/. No network access or shell escape is used.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', choices=('pdflatex', 'lualatex'), default='pdflatex')
    args = parser.parse_args()
    executable = shutil.which(args.engine)
    if executable is None:
        raise SystemExit(f'{args.engine} not found. Install TeX Live or MiKTeX with the packages used in article.tex.')
    out = ROOT / 'build'
    out.mkdir(exist_ok=True)
    command = [executable, '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', f'-output-directory={out}', 'article.tex']
    last = ''
    for n in range(1, 4):
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, errors='replace')
        last = run.stdout + '\n' + run.stderr
        (out / f'pass-{n}.txt').write_text(last, encoding='utf-8')
        if run.returncode:
            sys.stderr.write(last[-10000:])
            raise SystemExit(f'LaTeX pass {n} failed; inspect build/pass-{n}.txt.')
    if 'There were undefined references' in last or 'Label(s) may have changed' in last:
        raise SystemExit('References did not converge after three passes; inspect build/article.log.')
    shutil.copy2(out / 'article.pdf', ROOT / 'article.pdf')
    print(f'Built {ROOT / "article.pdf"}')
    if 'Overfull' in last:
        print('WARNING: overfull boxes were reported; inspect the rendered PDF.')

if __name__ == '__main__':
    main()
