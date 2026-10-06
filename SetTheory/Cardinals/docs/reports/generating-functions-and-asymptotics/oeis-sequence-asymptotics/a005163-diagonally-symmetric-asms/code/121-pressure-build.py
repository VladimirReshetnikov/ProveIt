#!/usr/bin/env python3
"""Build report121.pdf twice in clean directories and require byte equality.
Requires pdflatex/pdftex and the TeX packages named in report121.tex.
No network, installation, or source-file mutation is performed.
"""
from hashlib import sha256
from pathlib import Path
import os
import re
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def run_bounded(command, *, timeout, **kwargs):
    try:
        return subprocess.run(command, timeout=timeout, **kwargs)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f'SUBPROCESS_TIMEOUT after {timeout}s: {command[0]}') from exc

def build_once(destination):
    destination.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy()
    env.update(SOURCE_DATE_EPOCH='1790899200',FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXMFVAR']=str(destination/'texmf-var')
    env['TEXMFCONFIG']=str(destination/'texmf-config')
    env['TEXFORMATS']=str(destination)+'//:'
    fmt=['pdftex','-ini','-etex','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini']
    cp=run_bounded(fmt,timeout=120,cwd=destination,env=env,capture_output=True)
    (destination/'format.stdout').write_bytes(cp.stdout+cp.stderr)
    require(cp.returncode==0,'TeX format generation failed: '+(cp.stdout+cp.stderr).decode(errors='replace')[-8000:])
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{report121.tex}'
    command=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',f'-output-directory={destination}',source]
    for run in range(1,4):
        cp=run_bounded(command,timeout=180,cwd=ROOT,env=env,capture_output=True)
        (destination/f'pass{run}.stdout').write_bytes(cp.stdout+cp.stderr)
        require(cp.returncode==0,f'PDF build pass {run} failed: '+(cp.stdout+cp.stderr).decode(errors='replace')[-8000:])
    log=(destination/'report121.log').read_text(errors='replace')
    forbidden=r'Overfull \\[hv]box|undefined references|undefined citations|LaTeX Warning: (?:Reference|Citation)|Label\(s\) may have changed'
    matches=re.findall(forbidden,log)
    require(not matches,f'TeX quality gate failed: {matches}\n'+ '\n'.join(line for line in log.splitlines() if re.search(forbidden,line)))
    return (destination/'report121.pdf').read_bytes()

def main():
    with tempfile.TemporaryDirectory(prefix='report121-build-a-') as tmp:
        first=build_once(Path(tmp))
    with tempfile.TemporaryDirectory(prefix='report121-build-b-') as tmp:
        second=build_once(Path(tmp))
    require(first==second,'PDF is not byte-identical across clean builds')
    (ROOT/'report121.pdf').write_bytes(first)
    print('PASS: two clean builds are byte-identical; PDF SHA256 '+sha256(first).hexdigest())

if __name__=='__main__':
    main()
