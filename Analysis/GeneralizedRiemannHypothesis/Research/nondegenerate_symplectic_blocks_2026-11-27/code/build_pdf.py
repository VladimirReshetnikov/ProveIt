#!/usr/bin/env python3
"""Compile the paper offline using an installed TeX distribution.

Uses ordinary pdflatex when configured. If a Debian-style installed TeX tree
has no format/filename database, creates a private format and font map from
the installed files. Does not download anything or enable shell escape.
"""
from __future__ import annotations
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

root=Path(__file__).resolve().parents[1]
logs=[]

def run(args,cwd,env):
    process=subprocess.run(args,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(str(x) for x in args)+'\n'+process.stdout)
    if process.returncode:
        (root/'results/pdf_build.log').write_text('\n'.join(logs))
        raise RuntimeError(process.stdout[-6000:])

def configured():
    if not shutil.which('pdflatex') or not shutil.which('kpsewhich'):
        return False
    p=subprocess.run(['kpsewhich','pdflatex.fmt'],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
    return p.returncode==0 and bool(p.stdout.strip())

env=os.environ.copy()
with tempfile.TemporaryDirectory(prefix='symplectic-tex-') as work:
    tmp=Path(work)
    if configured():
        command=['pdflatex']
    else:
        dist=Path('/usr/share/texlive/texmf-dist')
        extra=Path('/usr/share/texmf')
        ini=dist/'tex/latex/tex-ini-files/pdflatex.ini'
        if not ini.is_file() or not shutil.which('pdftex'):
            raise RuntimeError('An installed TeX distribution with pdflatex is required; no network download was attempted.')
        def paths(*parts):
            return ':'.join(str(x)+'//' for x in parts)+':'
        env['TEXINPUTS']='.:'+paths(dist/'tex',extra/'tex')
        env['TFMFONTS']=paths(dist/'fonts/tfm',extra/'fonts/tfm')
        env['T1FONTS']=paths(dist/'fonts/type1',extra/'fonts/type1')
        env['ENCFONTS']=paths(dist/'fonts/enc',extra/'fonts/enc')
        env['VFFONTS']=paths(dist/'fonts/vf',extra/'fonts/vf')
        map_files=[extra/'fonts/map/dvips/lm/lm.map']
        map_files += [dist/('fonts/map/dvips/amsfonts/'+name+'.map') for name in ['cm','cmextra','latxfont','symbols']]
        (tmp/'pdftex.map').write_text('\n'.join(p.read_text() for p in map_files))
        env['TEXFONTMAPS']=paths(tmp,dist/'fonts/map',extra/'fonts/map')
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
             '-halt-on-error','-jobname=pdflatex','-progname=pdflatex',str(ini)],tmp,env)
        command=['pdflatex','-fmt='+str(tmp/'pdflatex.fmt')]
    for _ in range(3):
        run(command+['-no-shell-escape','-interaction=nonstopmode','-halt-on-error','paper.tex'],root,env)
(root/'results/pdf_build.log').write_text('\n'.join(logs))
assert (root/'paper.pdf').is_file()
print('Compiled paper.pdf offline; full log: results/pdf_build.log')
