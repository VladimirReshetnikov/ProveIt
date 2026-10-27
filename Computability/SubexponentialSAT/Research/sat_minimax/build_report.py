#!/usr/bin/env python3
"""Build the report with shell escape disabled and check the final TeX log."""
from pathlib import Path
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    if not shutil.which('pdflatex'):
        raise RuntimeError('Install pdfLaTeX and the packages listed in report.tex.')
    for iteration in range(3):
        proc = subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                               '-halt-on-error','report.tex'], cwd=ROOT,
                              capture_output=True,text=True)
        if proc.returncode:
            raise RuntimeError(proc.stdout[-6000:] + proc.stderr)
    log = (ROOT/'report.log').read_text(errors='replace')
    problems = re.findall(r'^.*(?:Overfull \\[hv]box|undefined|multiply defined|Rerun to get).*$',
                          log, re.MULTILINE)
    if problems:
        raise RuntimeError('Resolve report diagnostics:\n'+'\n'.join(problems))
    pages = re.search(r'Output written on report.pdf \((\d+) pages', log)
    receipt = {'status':'PASS','tex_passes':3,'shell_escape':False,
               'pages':int(pages.group(1)) if pages else None,
               'overfull_boxes':0,'unresolved_references':0}
    (ROOT/'results/pdf_build.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))


if __name__ == '__main__':
    main()
