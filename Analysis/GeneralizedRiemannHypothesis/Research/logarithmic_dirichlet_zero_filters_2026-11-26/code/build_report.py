#!/usr/bin/env python3
"""Build the report, using only a local fallback for uninitialized TeX files."""
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]

def kpse(name):
    return subprocess.run(['kpsewhich',name],capture_output=True,text=True).stdout.strip()

def main():
    env = os.environ.copy()
    if not shutil.which('latexmk') or not shutil.which('pdflatex'):
        raise SystemExit('Install a TeX distribution with pdflatex and latexmk.')
    build = ROOT/'.build'
    build.mkdir(exist_ok=True)
    if not kpse('pdflatex.fmt'):
        ini = kpse('pdflatex.ini')
        if not ini:
            raise SystemExit('pdflatex.ini is missing from the TeX distribution.')
        subprocess.run(['pdftex','-ini','-etex','-jobname=pdflatex',
                        '-progname=pdflatex',ini],cwd=build,check=True)
        env['TEXFORMATS'] = str(build)+os.pathsep+env.get('TEXFORMATS','')
    if not kpse('pdftex.map'):
        maps=[]
        lm=kpse('lm.map')
        cm=kpse('cm.map')
        if lm:
            maps.append(Path(lm))
        if cm:
            maps.extend(sorted(Path(cm).parent.glob('*.map')))
        if not maps:
            raise SystemExit('No suitable font maps found; initialize your TeX installation.')
        (build/'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
        env['TEXFONTMAPS'] = str(build)+os.pathsep+env.get('TEXFONTMAPS','')
    subprocess.run(['latexmk','-g','-pdf','-interaction=nonstopmode',
                    '-halt-on-error','logarithmic_zero_filters.tex'],
                   cwd=ROOT,env=env,check=True)

if __name__=='__main__':
    main()
