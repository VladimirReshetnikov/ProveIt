#!/usr/bin/env python3
"""Rebuild Research_Report39.pdf offline in a fresh external directory.

Requires Python3 and a local TeX Live pdfLaTeX installation. Shell escape is
explicitly disabled. No network access, package installation, or source mutation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
NAME = 'Research_Report39'
TEX_SOURCES = ('Research_Report39.tex',)
OPTIONAL_TEX_SOURCES = ()
EPOCH = '1790985600'


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def snapshot():
    out = {}
    for p in [ROOT]+sorted(ROOT.rglob('*')):
        s = p.lstat()
        need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsafe release path')
        out[p.relative_to(ROOT).as_posix()] = (hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return out


def run(cmd,cwd,env,log):
    with log.open('wb') as out:
        result = subprocess.run(cmd,cwd=cwd,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=300)
    need(result.returncode == 0,'PDF build command failed; inspect '+log.name)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',required=True,type=Path,help='new, empty directory outside this release')
    p.add_argument('--check-packaged',action='store_true',help='require a sealed identity and byte equality with the packaged PDF')
    a = p.parse_args()
    target = a.output.resolve()
    need(target != ROOT and ROOT not in target.parents,'PDF build directory must be external')
    need(not target.exists() or (target.is_dir() and not any(target.iterdir())),'PDF build directory must be new or empty')
    need(all((ROOT/name).is_file() for name in TEX_SOURCES),'Article source missing')
    before = snapshot()
    if a.check_packaged:
        checked = subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify_release.py'),'--verify-only'],capture_output=True,text=True,timeout=120)
        need(checked.returncode == 0,'Release identity failed: '+checked.stderr[-3000:])
    target.mkdir(parents=True,exist_ok=True)
    for name in TEX_SOURCES + OPTIONAL_TEX_SOURCES:
        if (ROOT/name).is_file():
            shutil.copy2(ROOT/name,target/name)
    cache = target/'tex-cache';cache.mkdir()
    env = dict(os.environ)
    env.update(TEXMFVAR=str(cache),TEXMFCONFIG=str(cache),TEXFORMATS=str(cache)+':',TZ='UTC',SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1')
    def kpse(name):
        proc = subprocess.run(['kpsewhich',name],cwd=target,env=env,capture_output=True,text=True)
        return proc.stdout.strip() if proc.returncode == 0 else ''
    if not kpse('article.cls'):
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    if not kpse('pdflatex.fmt'):
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env,cache/'format-build.log')
    if not kpse('pdftex.map'):
        raw = b''
        for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
            value = kpse(name)
            need(bool(value),'Missing TeX font map: '+name)
            raw += Path(value).read_bytes()+b'\n'
        (cache/'pdftex.map').write_bytes(raw)
        env['TEXFONTMAPS'] = str(cache)+':'
    texinput = r'\pdfinfoomitdate=1\pdftrailerid{}\input{'+NAME+'.tex}'
    for n in range(1,4):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname='+NAME,texinput],target,env,target/('compile-'+str(n)+'.log'))
    need(snapshot() == before,'Original release bytes/modes/mtimes changed during PDF build')
    result = target/(NAME+'.pdf')
    need(result.is_file(),'PDF output missing')
    digest = hashlib.sha256(result.read_bytes()).hexdigest()
    original = ROOT/result.name
    if a.check_packaged:
        need(original.is_file() and original.read_bytes() == result.read_bytes(),'Rebuilt PDF differs from the packaged PDF')
    print(json.dumps({'schema':'report39-pdf-build-v1','status':'PASS','pdf_filename':result.name,'pdf_sha256':digest,'pdf_bytes':result.stat().st_size,'original_bytes_modes_mtimes_preserved':True,'shell_escape':False,'source_date_epoch':int(EPOCH),'matches_packaged_pdf':original.is_file() and original.read_bytes()==result.read_bytes()},indent=2,sort_keys=True))


if __name__ == '__main__':main()
