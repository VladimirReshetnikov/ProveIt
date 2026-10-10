#!/usr/bin/env python3
"""Assemble the modular sources and build the deliverable PDF with latexmk."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
STEM='polylogarithm_stieltjes_continuation'


def expand(path,active=()):
    path=path.resolve()
    if path in active:raise ValueError('Circular TeX input: '+str(path))
    text=path.read_text(encoding='utf-8')
    pattern=re.compile(r'\\input\{([^}]+)\}')
    def replacement(match):
        child=ROOT/match.group(1)
        if not child.suffix:child=child.with_suffix('.tex')
        return ('\n% BEGIN '+str(child.relative_to(ROOT))+'\n'
                +expand(child,active+(path,))
                +'\n% END '+str(child.relative_to(ROOT))+'\n')
    return pattern.sub(replacement,text)


def main():
    assembled=ROOT/(STEM+'.tex')
    assembled.write_text('% Assembled from main.tex and article/*.tex.\n'
                         '% Rebuild with python code/build_article.py.\n'
                         +expand(ROOT/'main.tex'),encoding='utf-8')
    build=ROOT/'.build'
    build.mkdir(exist_ok=True)
    result=subprocess.run(['latexmk','-pdf','-interaction=nonstopmode','-halt-on-error',
                           '-outdir='+str(build),assembled.name],cwd=ROOT,
                           stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (ROOT/'verification'/'latex_build.log').write_text(result.stdout,encoding='utf-8')
    if result.returncode:
        print('\n'.join(result.stdout.splitlines()[-35:]))
        raise SystemExit(result.returncode)
    log=(build/(STEM+'.log')).read_text(errors='replace')
    forbidden=['undefined references','undefined on input line','Overfull \\hbox',
               'Overfull \\vbox','multiply defined']
    issues=[s for s in forbidden if s in log]
    shutil.copyfile(build/(STEM+'.pdf'),ROOT/(STEM+'.pdf'))
    receipt=dict(build_returncode=result.returncode,layout_or_reference_issues=issues,
                 assembled_tex_sha256=hashlib.sha256(assembled.read_bytes()).hexdigest(),
                 pdf_sha256=hashlib.sha256((ROOT/(STEM+'.pdf')).read_bytes()).hexdigest(),
                 status='PASS' if not issues else 'REVIEW REQUIRED',
                 visual_review='See the separate rendered-review record.')
    (ROOT/'verification'/'build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('Built',STEM+'.pdf')
    print('Reference/overflow audit:',receipt['status'])
    if issues:raise SystemExit(1)


if __name__=='__main__':main()
