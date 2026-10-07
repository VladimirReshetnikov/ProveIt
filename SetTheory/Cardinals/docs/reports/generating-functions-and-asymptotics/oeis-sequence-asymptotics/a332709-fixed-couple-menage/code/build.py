#!/usr/bin/env python3
"""Portable deterministic reproduction of Report221; no network access needed."""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

ROOT=Path(__file__).resolve().parent
WORK=ROOT/'.build'
EPOCH='1791072000'  # 2026-10-04 00:00:00 UTC
MEMBERS=['Report221.tex','Report221.pdf','README.md','SOURCES.md','source_pins.json',
         'build.py','requirements.txt','code/menage.py','code/check_exact.py',
         'code/diagnostics.py','receipts/exact.json','receipts/exact_optimized.json',
         'receipts/exact_low_digit_cap.json','receipts/exact_low_digit_cap_optimized.json',
         'receipts/diagnostics.json']


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def run(command, cwd=ROOT, env=None, timeout=600):
    p=subprocess.run(command,cwd=cwd,env=env,capture_output=True,timeout=timeout)
    require(p.returncode==0,"Command failed: "+str(command)+"\n"+(p.stdout+p.stderr).decode(errors='replace')[-12000:])
    return p.stdout


def checks():
    (ROOT/'receipts').mkdir(exist_ok=True)
    outputs=[]
    for optimized, cap, name in [(False,None,'exact'),(True,None,'exact_optimized'),
                                 (False,'640','exact_low_digit_cap'),(True,'640','exact_low_digit_cap_optimized')]:
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
        if cap is not None: env['PYTHONINTMAXSTRDIGITS']=cap
        command=[sys.executable]+(['-O'] if optimized else [])+['code/check_exact.py']
        data=run(command,env=env)
        require(json.loads(data)['passed'] is True,'exact receipt did not pass')
        (ROOT/'receipts'/f'{name}.json').write_bytes(data)
        outputs.append(data)
    require(all(data==outputs[0] for data in outputs),'normal, optimized and digit-cap receipts differ')
    require(importlib.metadata.version('mpmath')=='1.3.0','mpmath 1.3.0 required for identical diagnostics')
    data=run([sys.executable,'code/diagnostics.py'])
    require(json.loads(data)['diagnostic_only'] is True,'diagnostics must be explicitly labeled')
    (ROOT/'receipts/diagnostics.json').write_bytes(data)


def prepare_tex():
    WORK.mkdir(exist_ok=True)
    paths={}
    for name in ('home','tmp','texvar','texconfig','texcache','texhome','fonts'):
        p=WORK/name;p.mkdir(exist_ok=True);paths[name]=str(p)
    env={'PATH':os.environ.get('PATH',os.defpath),'HOME':paths['home'],
         'TMPDIR':paths['tmp'],'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1',
         'TZ':'UTC','LC_ALL':'C','LANG':'C','max_print_line':'1000',
         'TEXMFVAR':paths['texvar'],'TEXMFCONFIG':paths['texconfig'],
         'TEXMFCACHE':paths['texcache'],'TEXMFHOME':paths['texhome'],
         'VARTEXFONTS':paths['fonts'],'openout_any':'p','shell_escape':'f'}
    require(shutil.which('kpsewhich') and shutil.which('pdftex') and shutil.which('pdflatex'),
            'TeX Live with pdftex, pdflatex and kpsewhich is required')
    dist=Path(run(['kpsewhich','-var-value=TEXMFDIST'],cwd=WORK,env=env).decode().strip())
    require(dist.is_dir(),'TeX distribution tree is missing')
    trees=[dist];sibling=dist.parent.parent/'texmf'
    if sibling.is_dir():trees.append(sibling)
    env['TEXMF']='{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS']=str(WORK)+os.pathsep
    env['TEXFONTMAPS']=str(WORK)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
         '-halt-on-error','-jobname=pdflatex','pdflatex.ini'],cwd=WORK,env=env)
    maps=[]
    for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
        p=Path(run(['kpsewhich',name],cwd=WORK,env=env).decode().strip())
        require(p.is_file(),'Missing font map '+name);maps.append(p.read_bytes())
    (WORK/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    return env


def pdf():
    env=prepare_tex()
    source=(r'\def\DoNotLoadEpstopdf{}\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15'
            r'\input{Report221.tex}')
    command=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',
             '-no-shell-escape','-jobname=Report221','-output-directory=.build',source]
    previous=None
    for k in range(6):
        output=run(command,env=env)
        (WORK/f'pass{k+1}.txt').write_bytes(output)
        state=tuple((WORK/('Report221.'+s)).read_bytes() if (WORK/('Report221.'+s)).exists() else b'' for s in ('aux','toc','out'))
        if k>=1 and state==previous:break
        previous=state
    else:raise RuntimeError('TeX references did not stabilize')
    log=(WORK/'Report221.log').read_text(errors='replace')
    failures=('undefined references','undefined citations','multiply-defined labels',
              'Rerun to get cross-references right','Label(s) may have changed','Missing character:','Overfull')
    require(not any(f in log for f in failures),'TeX reference/font/layout defect; inspect .build/Report221.log')
    shutil.copyfile(WORK/'Report221.pdf',ROOT/'Report221.pdf')


def package():
    for name in MEMBERS:
        p=ROOT/name
        require(p.is_file() and not p.is_symlink(),'Missing or linked public file '+name)
    manifest=''.join(hashlib.sha256((ROOT/n).read_bytes()).hexdigest()+'  '+n+'\n' for n in sorted(MEMBERS))
    (ROOT/'MANIFEST.sha256').write_text(manifest,encoding='ascii')
    names=sorted(MEMBERS+['MANIFEST.sha256'])
    with zipfile.ZipFile(ROOT/'Report221.zip','w',compression=zipfile.ZIP_STORED) as z:
        for name in names:
            info=zipfile.ZipInfo(name,(2026,10,4,0,0,0));info.create_system=3
            info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_STORED
            z.writestr(info,(ROOT/name).read_bytes())
    with zipfile.ZipFile(ROOT/'Report221.zip') as z:
        require(z.testzip() is None and z.namelist()==names,'archive validation failed')
        for name in names:
            require(z.read(name)==(ROOT/name).read_bytes(),'archive member differs: '+name)
    print(json.dumps({'pdf_sha256':hashlib.sha256((ROOT/'Report221.pdf').read_bytes()).hexdigest(),
                      'zip_sha256':hashlib.sha256((ROOT/'Report221.zip').read_bytes()).hexdigest(),
                      'archive_members':len(names)},sort_keys=True,indent=2))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checks-only',action='store_true')
    parser.add_argument('--pdf-only',action='store_true')
    parser.add_argument('--package-only',action='store_true')
    args=parser.parse_args()
    require(sum((args.checks_only,args.pdf_only,args.package_only))<=1,'choose at most one mode')
    if args.package_only:package();return
    if args.pdf_only:pdf();return
    checks()
    if args.checks_only:return
    pdf();package()

if __name__=='__main__':main()
