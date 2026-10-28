#!/usr/bin/env python3
"""Build the manuscript without shell escape and reject layout/reference errors."""
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    if shutil.which('pdflatex') is None:
        raise RuntimeError('pdflatex is required to build the manuscript')
    build = ROOT/'build'
    build.mkdir(exist_ok=True)
    # Ignore auxiliary files left by an interrupted earlier build.
    for suffix in ('aux', 'out', 'toc'):
        (build/('report.'+suffix)).unlink(missing_ok=True)
    for pass_number in range(3):
        completed = subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                                    '-halt-on-error','-output-directory=build','report.tex'],
                                   cwd=ROOT,capture_output=True,text=True)
        (build/('pass_'+str(pass_number+1)+'.txt')).write_text(completed.stdout+completed.stderr)
        if completed.returncode:
            raise RuntimeError('LaTeX build failed; inspect '+str(build/('pass_'+str(pass_number+1)+'.txt')))
    log = (build/'report.log').read_text()
    bad = ['Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations',
           'There were undefined','Rerun to get cross-references right']
    if any(marker in log for marker in bad):
        raise RuntimeError('LaTeX layout/reference check failed; inspect build/report.log')
    shutil.copyfile(build/'report.pdf',ROOT/'report.pdf')
    print('Built '+str(ROOT/'report.pdf'))


if __name__ == '__main__':
    main()
