#!/usr/bin/env python3
"""Compile the supplied paper without changing the sealed release PDF."""
import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT.parent / 'report-rebuilt.pdf')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError('Choose an output outside the sealed release directory.')
    engine = shutil.which('pdflatex')
    if engine is None:
        raise SystemExit('pdflatex was not found. Install TeX Live or MiKTeX with the packages used in report.tex.')
    with tempfile.TemporaryDirectory(prefix='pa_unary_tex_') as directory:
        build = Path(directory)
        command = [engine, '-interaction=nonstopmode', '-halt-on-error',
                   '-no-shell-escape', '-output-directory=' + str(build), 'report.tex']
        for _ in range(3):
            run = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
            if run.returncode:
                raise SystemExit(run.stdout[-12000:] + run.stderr[-3000:])
        log = (build / 'report.log').read_text(encoding='utf-8', errors='replace')
        issues = [line for line in log.splitlines()
                  if any(word in line for word in ('Overfull', 'LaTeX Warning:', 'Package hyperref Warning:'))]
        if issues:
            print('\n'.join(issues))
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(build / 'report.pdf', output)
    print(str(output))
    print('PDF bytes may differ with TeX versions and build timestamps. Mathematical source is the release reference.')


if __name__ == '__main__':
    main()
