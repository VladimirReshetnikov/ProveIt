#!/usr/bin/env python3
"""Build the self-contained LaTeX report with pdflatex; no network access."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='pdflatex')
    args = parser.parse_args()
    executable = shutil.which(args.engine)
    if executable is None:
        raise SystemExit(f'LaTeX executable not found: {args.engine}')
    (ROOT / 'results').mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='zfc-subset-report-') as temp:
        work = Path(temp)
        shutil.copy2(ROOT / 'report.tex', work / 'report.tex')
        log = []
        for i in range(3):
            completed = subprocess.run(
                [executable, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log.append(f'PASS {i + 1}\n{completed.stdout}')
            if completed.returncode:
                (ROOT / 'results' / 'pdf-build.log').write_text('\n'.join(log), encoding='utf-8')
                raise SystemExit('LaTeX compilation failed; see results/pdf-build.log')
        shutil.copy2(work / 'report.pdf', ROOT / 'report.pdf')
        final_log = (work / 'report.log').read_text(encoding='utf-8', errors='replace')
        (ROOT / 'results' / 'pdf-build.log').write_text(final_log, encoding='utf-8')
    print(ROOT / 'report.pdf')


if __name__ == '__main__':
    main()
