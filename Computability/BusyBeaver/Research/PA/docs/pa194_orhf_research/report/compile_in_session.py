#!/usr/bin/env python3
"""Compile this report from installed TeX sources without system cache writes.

This Linux helper handles the session's dangling /var/lib/texmf symlinks.
It builds a private pdfLaTeX format and font map in a writable work area;
all installed TeX packages and fonts remain read-only. No network is used.
With a normal TeX installation, ordinary pdflatex is sufficient instead.
"""
from pathlib import Path
import argparse, os, subprocess

def execute(argv, cwd, env, log):
    with log.open('w') as output:
        result=subprocess.run(argv,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT)
    if result.returncode:
        tail='\n'.join(log.read_text(errors='replace').splitlines()[-35:])
        raise RuntimeError(f'Command failed ({result.returncode}); see {log}\n{tail}')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('document',type=Path)
    parser.add_argument('--workarea',type=Path,default=Path('/tmp/pa194_tex'))
    parser.add_argument('--passes',type=int,default=3)
    args=parser.parse_args()
    document=args.document.resolve();work=args.workarea.resolve()
    if not document.is_file():raise FileNotFoundError(document)
    if args.passes<1:raise ValueError('--passes must be positive')
    for suffix in ('var','config','maps'):(work/suffix).mkdir(parents=True,exist_ok=True)
    roots=[work,Path('/etc/texmf'),Path('/usr/share/texmf'),Path('/usr/share/texlive/texmf-dist')]
    if not (roots[-1]/'tex/latex/base/latex.ltx').exists():raise FileNotFoundError('Installed LaTeX sources are missing')
    env=os.environ.copy()
    env.update(TEXMF='{'+','.join(map(str,roots))+'}',TEXMFVAR=str(work/'var'),TEXMFCONFIG=str(work/'config'),TEXFORMATS=str(work)+'//',TEXFONTMAPS=str(work/'maps')+'//:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//')
    sources=[Path('/usr/share/texmf/fonts/map/dvips/lm/lm.map')]+sorted(Path('/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts').glob('*.map'))
    seen=set();entries=[]
    for source in sources:
        for line in source.read_text().splitlines():
            if not line.strip()or line.lstrip().startswith(('%','#')):continue
            name=line.split()[0]
            if name not in seen:entries.append(line);seen.add(name)
    (work/'maps/pdftex.map').write_text('\n'.join(entries)+'\n')
    fmt=work/'pdflatex.fmt'
    if not fmt.is_file():
        execute(['pdftex','-ini','-etex','-jobname=pdflatex','-progname=pdflatex','-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],work,env,work/'format-build.log')
    for pass_number in range(1,args.passes+1):
        execute(['pdflatex','-fmt='+str(fmt),'-interaction=nonstopmode','-halt-on-error',document.name],document.parent,env,work/f'report-pass{pass_number}.log')
        print(f'Completed TeX pass {pass_number}',flush=True)
    output=document.with_suffix('.pdf')
    if not output.is_file():raise RuntimeError('No PDF was emitted')
    print(f'PDF: {output} ({output.stat().st_size} bytes)',flush=True)
if __name__=='__main__':main()
