#!/usr/bin/env python3
"""Run reference checks and compile the report. No network or upstream build.

The pinned table audit is optional and requires --table PATH, because no
upstream table is redistributed. Run without Python optimization: the finite
experiments use assertions. PDF rebuilding requires pdflatex on PATH.
"""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(args: list[str], log: Path) -> None:
    with log.open('w', encoding='utf-8') as f:
        result = subprocess.run(args, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}); see {log}')


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tests', action='store_true')
    p.add_argument('--skip-pdf', action='store_true')
    p.add_argument('--table', type=Path)
    args = p.parse_args()
    if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        p.error('Run without -O or PYTHONOPTIMIZE; experiments use assertions.')
    results = ROOT / 'results'
    results.mkdir(exist_ok=True)
    if args.tests:
        run([sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
            results / 'tests.txt')
        run([sys.executable, 'code/metrics.py'], results / 'metrics_run.txt')
        run([sys.executable, 'code/experiments.py'], results / 'experiments_run.txt')
        run([sys.executable, 'code/logic.py', 'examples/identity.json'],
            results / 'example_check.json')
        run([sys.executable, 'code/codec.py', '--stop', '10000'],
            results / 'bounded_search.txt')
    if args.table:
        run([sys.executable, 'code/tm_audit.py', str(args.table.resolve()),
             '--steps', '264982', '--out', str(results / 'tm_audit.json')],
            results / 'tm_audit_run.txt')
    if not args.skip_pdf:
        executable = shutil.which('pdflatex')
        if not executable:
            raise RuntimeError('pdflatex not found; use --skip-pdf for Python checks only.')
        build = ROOT / '.build'
        build.mkdir(exist_ok=True)
        command = [executable, '-interaction=nonstopmode', '-halt-on-error',
                   '-file-line-error', '-output-directory', str(build),
                   str(ROOT / 'article/report.tex')]
        for i in range(3):
            run(command, build / f'pass-{i+1}.txt')
        shutil.copy2(build / 'report.pdf', ROOT / 'article/report.pdf')
        print('PDF: article/report.pdf')
    print('Requested checks completed. Logs are in results/ and .build/.')


if __name__ == '__main__':
    main()
