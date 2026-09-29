#!/usr/bin/env python3
"""Build the article with an installed TeX distribution; optionally run tests."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='run finite checks before building')
    args = parser.parse_args()
    try:
        if args.verify:
            subprocess.run([sys.executable, 'code/verify.py'], cwd=ROOT, check=True)
        if shutil.which('latexmk'):
            subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode',
                            '-halt-on-error', 'article.tex'], cwd=ROOT, check=True)
        elif shutil.which('pdflatex'):
            for _ in range(3):
                subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                '-halt-on-error', 'article.tex'], cwd=ROOT, check=True)
        else:
            print('Install a TeX distribution providing pdflatex or latexmk.', file=sys.stderr)
            return 2
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f'Build failed: {exc}', file=sys.stderr)
        return 1
    print(f'Built: {ROOT / "article.pdf"}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
