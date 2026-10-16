#!/usr/bin/env python3
"""Reproduce formula metrics, optional regressions, and the PDF.

Python 3.10+, standard library only. PDF building additionally requires pdflatex
and the packages in the article preamble. No network access is performed.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run_logged(command: list[str], log: Path) -> None:
    with log.open('w', encoding='utf-8') as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream,
                                stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        tail = '\n'.join(log.read_text(encoding='utf-8', errors='replace').splitlines()[-40:])
        raise RuntimeError(f'Command failed ({result.returncode}): {command[0]}\n{tail}\nLog: {log}')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tests', action='store_true', help='Run all finite regression checks.')
    parser.add_argument('--skip-pdf', action='store_true', help='Do not invoke pdflatex.')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required.')
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    (ROOT / 'results').mkdir(exist_ok=True)
    run_logged([sys.executable, 'code/formulas.py'], build / 'metrics.log')
    print('Formula templates and metrics reproduced.')
    if args.tests:
        # Explicitly disable optimization: assertions are the regression checks.
        command = [sys.executable, '-E', '-X', 'dev', 'code/experiments.py']
        run_logged(command, build / 'experiments.log')
        print('All finite regression checks passed (results/experiments.json).')
    if not args.skip_pdf:
        exe = shutil.which('pdflatex')
        if exe is None:
            raise RuntimeError('pdflatex was not found. Install a TeX distribution, '
                               'or use --skip-pdf to reproduce Python results only.')
        for i in range(1, 4):
            run_logged([exe, '-interaction=nonstopmode', '-halt-on-error',
                        '-output-directory=.build', 'article/seeded_closure_zfc.tex'],
                       build / f'pdflatex-{i}.log')
        log = (build / 'seeded_closure_zfc.log').read_text(encoding='utf-8', errors='replace')
        errors = ('There were undefined references', 'LaTeX Warning: Citation',
                  'LaTeX Warning: Reference', 'Overfull \\hbox', 'Overfull \\vbox')
        if any(marker in log for marker in errors):
            raise RuntimeError('The PDF built, but layout/reference QA found a warning. '
                               'Inspect .build/seeded_closure_zfc.log.')
        shutil.copy2(build / 'seeded_closure_zfc.pdf', ROOT / 'article/seeded_closure_zfc.pdf')
        print('PDF built: article/seeded_closure_zfc.pdf')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError) as error:
        print(f'Build error: {error}', file=sys.stderr)
        raise SystemExit(1)
