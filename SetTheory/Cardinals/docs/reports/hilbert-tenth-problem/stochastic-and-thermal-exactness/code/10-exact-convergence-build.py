#!/usr/bin/env python3
"""Reproduce tests/exports and build the standalone article with pdfLaTeX."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-tests', action='store_true',
                        help='build only the PDF using existing artifacts')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    latex = shutil.which('pdflatex')
    if latex is None:
        parser.error('pdflatex is not on PATH; install TeX Live or MiKTeX first')
    if not args.skip_tests:
        process = subprocess.run([sys.executable, str(root/'code'/'run_checks.py')],
                                 cwd=root, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
        (root/'artifacts'/'test_run.txt').write_text(process.stdout, encoding='utf-8')
        print(process.stdout, end='')
        if process.returncode:
            return process.returncode
    logs = root/'build_logs'
    logs.mkdir(exist_ok=True)
    for pass_number in range(1, 4):
        process = subprocess.run(
            [latex, '-interaction=nonstopmode', '-halt-on-error', 'article.tex'],
            cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/f'pdflatex-{pass_number}.txt'
        log.write_text(process.stdout, encoding='utf-8')
        if process.returncode:
            print(f'PDF build failed. See {log}', file=sys.stderr)
            return process.returncode
    print(f'Built {root / "article.pdf"}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
