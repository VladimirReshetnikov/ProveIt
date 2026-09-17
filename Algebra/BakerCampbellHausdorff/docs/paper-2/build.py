#!/usr/bin/env python3
"""Rebuild the paper; optionally regenerate and verify its exact coefficient data.

Usage:
    python build.py
    python build.py --verify

Python 3.9+, standard library only. A TeX installation with latexmk or pdflatex
must be on PATH. All intermediate TeX files are written to .build/.
"""
from __future__ import annotations
import argparse
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def run(command: list[str]) -> None:
    print('+ ' + ' '.join(command), flush=True)
    subprocess.run(command, cwd=ROOT, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true',
                        help='regenerate degree-12 data and run independent checks through degree 10')
    args = parser.parse_args()
    try:
        if args.verify:
            run([sys.executable, str(ROOT / 'code' / 'verify_bch.py'),
                 '--degree', '12', '--check-degree', '10'])
            run([sys.executable, str(ROOT / 'code' / 'make_tables.py')])
        target = ROOT / '.build'
        target.mkdir(exist_ok=True)
        latexmk = shutil.which('latexmk')
        pdflatex = shutil.which('pdflatex')
        if latexmk:
            run([latexmk, '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                 '-outdir=' + str(target), 'paper.tex'])
        elif pdflatex:
            command = [pdflatex, '-interaction=nonstopmode', '-halt-on-error',
                       '-output-directory=' + str(target), 'paper.tex']
            for _ in range(3):
                run(command)
        else:
            raise RuntimeError('Neither latexmk nor pdflatex was found on PATH. '
                               'The prebuilt paper.pdf remains available.')
        pdf = target / 'paper.pdf'
        if not pdf.is_file():
            raise RuntimeError('The TeX command completed without creating paper.pdf.')
        shutil.copy2(pdf, ROOT / 'paper.pdf')
        print('Created ' + str(ROOT / 'paper.pdf'))
        return 0
    except (OSError, RuntimeError, subprocess.CalledProcessError) as exc:
        print('Build failed: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
