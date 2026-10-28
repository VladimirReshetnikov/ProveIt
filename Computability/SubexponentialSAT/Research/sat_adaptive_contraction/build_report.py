#!/usr/bin/env python3
"""Build the complete report with local pdfLaTeX; no shell escape/network."""
from pathlib import Path
import json
import shutil
import subprocess

root=Path(__file__).resolve().parent
build=root/'_build'
build.mkdir(exist_ok=True)
engine=shutil.which('pdflatex')
if engine is None:
    raise SystemExit('pdfLaTeX is required to build the supplied source.')
command=[engine,'-interaction=nonstopmode','-halt-on-error','-no-shell-escape',
         '-output-directory',str(build),'adaptive_sat_review.tex']
for run in range(3):
    result=subprocess.run(command,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (build/f'pass_{run+1}.txt').write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-6000:])
        raise SystemExit(result.returncode)
log=(build/'adaptive_sat_review.log').read_text()
problems=[line for line in log.splitlines() if 'Overfull ' in line or 'undefined' in line.lower()]
if problems:
    raise SystemExit('Resolve report build warnings: '+repr(problems))
destination=root/'adaptive_sat_review.pdf'
shutil.copy2(build/destination.name,destination)
record={'status':'PASS','engine':engine,'passes':3,'shell_escape':False,
        'overfull_or_undefined_warnings':problems,'pdf_bytes':destination.stat().st_size}
(root/'results/pdf_build.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
