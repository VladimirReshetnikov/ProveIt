#!/usr/bin/env python3
"""Build report.pdf with a system format, or an isolated local-format fallback."""
from pathlib import Path
import os,shutil,subprocess

ROOT=Path(__file__).resolve().parent

def run(args,cwd,env):
    subprocess.run(args,cwd=cwd,env=env,check=True)

def main():
    env=os.environ.copy()
    if not shutil.which('pdftex'):
        raise SystemExit('Install TeX Live with pdfTeX and the packages in report.tex.')
    found=subprocess.run(['kpsewhich','pdflatex.fmt'],capture_output=True,text=True,env=env)
    format_path=found.stdout.strip()
    if found.returncode==0 and format_path and Path(format_path).is_file():
        command=['pdflatex','-interaction=nonstopmode','-halt-on-error','report.tex']
    else:
        trees=[p for p in('/usr/share/texlive/texmf-dist','/usr/share/texmf','/var/lib/texmf','/etc/texmf')if Path(p).is_dir()]
        if not trees:
            raise SystemExit('No usable TeX source tree was found for the local format.')
        env['TEXMF']='{.,'+','.join(trees)+'}'
        local=ROOT/'.tex-build';local.mkdir(exist_ok=True)
        if not(local/'pdflatex.fmt').is_file():
            run(['pdftex','-ini','-etex','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],local,env)
        command=['pdftex','-fmt='+str(local/'pdflatex'),'-progname=pdflatex','-interaction=nonstopmode','-halt-on-error','report.tex']
    run(command,ROOT,env)
    run(command,ROOT,env)
    print(ROOT/'report.pdf')

if __name__=='__main__':main()
