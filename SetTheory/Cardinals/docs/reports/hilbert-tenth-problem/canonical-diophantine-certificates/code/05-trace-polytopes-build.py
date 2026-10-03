#!/usr/bin/env python3
"""Verify examples and rebuild the article. Python 3.10+, standard library."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--verify-only', action='store_true')
    modes.add_argument('--skip-tests', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if not args.skip_tests:
        for script in ('verify.py', 'demo.py'):
            subprocess.run([sys.executable, '-B', str(root/'code'/script)],
                           cwd=root, check=True)
    if not args.verify_only:
        engine = shutil.which('pdflatex')
        if engine is None:
            parser.error('pdflatex is not installed or not on PATH; '
                         'use --verify-only to run just the Python checks.')
        for _ in range(3):
            subprocess.run([engine, '-interaction=nonstopmode',
                            '-halt-on-error', 'article.tex'], cwd=root, check=True)
        print('Built', root/'article.pdf')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as exc:
        print(f'Build failed: command exited with status {exc.returncode}', file=sys.stderr)
        raise SystemExit(exc.returncode) from exc
