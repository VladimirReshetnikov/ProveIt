#!/usr/bin/env python3
"""Compile the complete LaTeX report without shell escape or network access."""
from pathlib import Path
import json
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]


def main():
    if not shutil.which('pdflatex'):
        raise RuntimeError('Install pdfLaTeX and the packages listed in report.tex.')
    build=ROOT/'_build'
    build.mkdir(exist_ok=True)
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
             '-output-directory='+str(build),'report.tex']
    for run in range(3):
        result=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,text=True)
        (build/f'pass_{run+1}.txt').write_text(result.stdout)
        if result.returncode:
            raise RuntimeError('LaTeX failed: '+result.stdout[-4000:])
    log=(build/'report.log').read_text(errors='replace')
    forbidden=['Overfull \\hbox','Overfull \\vbox','There were undefined references',
               'Label(s) may have changed','multiply defined']
    failures=[x for x in forbidden if x in log]
    if failures:
        raise RuntimeError('PDF layout/reference check failed: '+repr(failures))
    shutil.copy2(build/'report.pdf',ROOT/'report.pdf')
    print(json.dumps({'status':'PASS','output':str(ROOT/'report.pdf'),
                      'bytes':(ROOT/'report.pdf').stat().st_size,'latex_passes':3}))


if __name__ == '__main__':
    main()
