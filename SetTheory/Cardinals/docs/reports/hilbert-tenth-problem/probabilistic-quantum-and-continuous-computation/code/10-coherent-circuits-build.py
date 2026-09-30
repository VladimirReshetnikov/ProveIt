#!/usr/bin/env python3
"""Build the article with pdfLaTeX; optionally rerun all exact checks.

    python build.py
    python build.py --check

Python >=3.10. A TeX installation with the packages named in article.tex is
required for the PDF, but the Python checks need only the standard library.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent


def logged(command: list[str], destination: Path) -> None:
    with destination.open('w',encoding='utf-8') as log:
        subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='rerun exact arithmetic tests first')
    args=parser.parse_args()
    try:
        if args.check:
            logged([sys.executable,'code/verify.py'],ROOT/'data/verification.log')
            logged([sys.executable,'code/check_certificate.py',
                    'data/HH_expanded_quartic.json','data/HH_zero_certificate.json',
                    'data/HTH_zero_certificate.json'],ROOT/'data/independent_checker.log')
            print('Exact checks passed.')
        executable=shutil.which('pdflatex')
        if executable is None:
            raise FileNotFoundError('pdflatex is not on PATH; install a TeX distribution to build the PDF.')
        build=ROOT/'_build';build.mkdir(exist_ok=True)
        for i in range(1,4):
            logged([executable,'-interaction=nonstopmode','-halt-on-error',
                    '-output-directory=_build','article.tex'],build/f'pass{i}.txt')
        shutil.copy2(build/'article.pdf',ROOT/'article.pdf')
        print(f'Built {ROOT/"article.pdf"}')
        return 0
    except (OSError,subprocess.CalledProcessError) as error:
        print(f'Build failed: {error}\nInspect data/verification.log or _build/pass*.txt.',file=sys.stderr)
        return 1


if __name__=='__main__': raise SystemExit(main())
