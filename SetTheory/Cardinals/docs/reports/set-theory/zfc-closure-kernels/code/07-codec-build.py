#!/usr/bin/env python3
"""Reproduce the local tests and build the report; no network access required."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run_tests() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O; experiment assertions must remain enabled')
    data = ROOT / 'data'
    data.mkdir(exist_ok=True)
    result = subprocess.run(
        [sys.executable, '-m', 'unittest', 'discover', '-s', 'code', '-v'],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False,
    )
    (data / 'unit_tests.txt').write_text(result.stdout, encoding='utf-8')
    print(result.stdout, end='')
    result.check_returncode()
    subprocess.run([sys.executable, 'code/experiments.py'], cwd=ROOT, check=True)
    for example in ('identity.json', 'schema_example.json'):
        check = subprocess.run(
            [sys.executable, 'code/checker.py', f'data/{example}'],
            cwd=ROOT, text=True, capture_output=True, check=True,
        )
        (data / f'{Path(example).stem}_check.json').write_text(
            check.stdout, encoding='utf-8'
        )

def build_pdf() -> None:
    engine = shutil.which('pdflatex')
    if engine is None:
        raise RuntimeError('pdflatex is required; use --skip-pdf to run only tests')
    with tempfile.TemporaryDirectory(prefix='zfc-tm-report-') as temporary:
        work = Path(temporary)
        shutil.copy2(ROOT / 'article/report.tex', work / 'report.tex')
        for iteration in range(3):
            result = subprocess.run(
                [engine, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                cwd=work, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, check=False,
            )
            if result.returncode:
                (ROOT / 'data/build_error.txt').write_text(result.stdout)
                result.check_returncode()
        log = (work / 'report.log').read_text(errors='replace')
        if 'Overfull \\hbox' in log or 'undefined references' in log:
            raise RuntimeError('Document needs layout/reference review; see TeX log')
        shutil.copy2(work / 'report.pdf', ROOT / 'article/report.pdf')
        (ROOT / 'data/latex_build.txt').write_text(log, encoding='utf-8')
        print('Built article/report.pdf')

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tests', action='store_true', help='rerun all local tests')
    parser.add_argument('--skip-pdf', action='store_true', help='do not invoke TeX')
    args = parser.parse_args()
    if args.tests:
        run_tests()
    if not args.skip_pdf:
        build_pdf()

if __name__ == '__main__':
    main()
