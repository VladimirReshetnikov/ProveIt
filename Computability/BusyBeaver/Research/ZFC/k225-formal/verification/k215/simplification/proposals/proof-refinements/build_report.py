#!/usr/bin/env python3
"""Compile the LaTeX report twice, keeping intermediates outside the package."""
from pathlib import Path
import argparse, shutil, subprocess, tempfile
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'report.pdf')
p.add_argument('--build-dir',type=Path)
a=p.parse_args()
out=a.build_dir or Path(tempfile.mkdtemp(prefix='k215-report-'))
out.mkdir(parents=True,exist_ok=True)
for run in (1,2):
    cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error',
         '-output-directory',str(out.resolve()),'report.tex']
    r=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/f'pass{run}.log').write_text(r.stdout)
    if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
a.output.parent.mkdir(parents=True,exist_ok=True)
shutil.copyfile(out/'report.pdf',a.output)
print(a.output.resolve())
print('Build log:',out/'report.log')
