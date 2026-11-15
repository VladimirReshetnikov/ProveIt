#!/usr/bin/env python3
"""Compile the standalone report with a normal pdflatex installation."""
import argparse,subprocess,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def main():
    p=argparse.ArgumentParser();p.add_argument('--engine',default='pdflatex');a=p.parse_args()
    out=ROOT/'report_build';out.mkdir(exist_ok=True)
    for i in (1,2):
        r=subprocess.run([a.engine,'-interaction=nonstopmode','-halt-on-error','-output-directory='+str(out),str(ROOT/'pa194_research_report.tex')],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/f'compile_pass{i}.log').write_text(r.stdout)
        if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
    shutil.copy2(out/'pa194_research_report.pdf',ROOT/'pa194_research_report.pdf')
    print(ROOT/'pa194_research_report.pdf')
if __name__=='__main__':main()
