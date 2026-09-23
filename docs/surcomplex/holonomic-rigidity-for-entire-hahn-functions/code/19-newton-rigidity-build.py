#!/usr/bin/env python3
"""Rebuild the standalone article; optionally run its exact finite checks."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='Run exact finite checks first.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if args.verify:
        subprocess.run([sys.executable, str(root / 'code' / 'verify.py')], cwd=root, check=True)
    engine = shutil.which('pdflatex')
    if engine is None:
        parser.error('pdflatex is not on PATH. Install TeX Live or MiKTeX, then retry.')
    for pass_number in range(1, 4):
        print(f'LaTeX pass {pass_number}/3', flush=True)
        subprocess.run([engine, '-interaction=nonstopmode', '-halt-on-error', 'article.tex'],
                       cwd=root, check=True)
    print(f'Built: {root / "article.pdf"}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as error:
        print(f'Build/verification command failed with exit code {error.returncode}.', file=sys.stderr)
        raise SystemExit(error.returncode) from error
