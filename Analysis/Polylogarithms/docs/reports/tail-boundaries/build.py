#!/usr/bin/env python3
"""Flatten the modular source and build the distributable PDF."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
STEM='Tail_Kernels_and_Boundary_Products'


def flatten(path,stack=()):
    path=path.resolve()
    if path in stack:raise RuntimeError(f'Cyclic TeX input: {path}')
    text=path.read_text(encoding='utf-8')
    def include(match):
        target=path.parent/match.group(1)
        if not target.suffix:target=target.with_suffix('.tex')
        return '\n% BEGIN '+str(target.relative_to(ROOT))+'\n'+flatten(target,stack+(path,))+'\n% END '+str(target.relative_to(ROOT))+'\n'
    return re.sub(r'(?m)^\s*\\input\{([^}]+)\}\s*$',include,text)


def main():
    target=ROOT/(STEM+'.tex')
    target.write_text(flatten(ROOT/'article.tex'),encoding='utf-8')
    build=ROOT/'build';build.mkdir(exist_ok=True)
    if shutil.which('latexmk'):
        args=['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error','-outdir=build',target.name]
        subprocess.run(args,cwd=ROOT,check=True)
    else:
        args=['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory=build',target.name]
        for _ in range(3):subprocess.run(args,cwd=ROOT,check=True)
    log=(build/(STEM+'.log')).read_text(errors='replace')
    for message in ['There were undefined references','There were multiply-defined labels']:
        if message in log:raise RuntimeError(message)
    shutil.copy2(build/(STEM+'.pdf'),ROOT/(STEM+'.pdf'))
    print(f'Created {target.name} and {STEM}.pdf')


if __name__=='__main__':main()
