#!/usr/bin/env python3
"""Build the PDF offline with fixed metadata in private temporary storage.
Requires an existing TeX Live installation. Never replaces an existing output.
"""
from pathlib import Path
import argparse
import os
import re
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
SOURCES=('Report211.tex',)

def need(ok,message):
    if not ok:
        raise RuntimeError(message)

def run(cmd,cwd,env):
    p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=180)
    need(p.returncode==0,'command failed: '+' '.join(cmd)+'\n'+(p.stdout+p.stderr)[-9000:])
    return p.stdout.strip()

p=argparse.ArgumentParser()
p.add_argument('--output',type=Path,required=True)
p.add_argument('--logs-dir',type=Path)
a=p.parse_args()
need(not a.output.exists(),'Output already exists; choose a fresh path')
if a.logs_dir:
    need(not a.logs_dir.exists(),'Logs directory already exists')
with tempfile.TemporaryDirectory(prefix='report211-build-') as temporary:
    base=Path(temporary); work=base/'tex';work.mkdir()
    env={'PATH':os.environ.get('PATH',os.defpath),'SOURCE_DATE_EPOCH':'1791072000',
         'FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C.UTF-8','openin_any':'p',
         'openout_any':'p','shell_escape':'f'}
    for key in ('HOME','TMPDIR','TEXMFVAR','TEXMFCONFIG','TEXMFCACHE','TEXMFHOME','VARTEXFONTS'):
        path=base/key;path.mkdir();env[key]=str(path)
    for name in SOURCES:
        source=ROOT/name
        need(source.is_file() and not source.is_symlink(),'Invalid source '+name)
        shutil.copyfile(source,work/name)
    probe=subprocess.run(['kpsewhich','pdflatex.fmt'],cwd=work,env=env,capture_output=True,text=True)
    if probe.returncode or not probe.stdout.strip():
        dist=Path(run(['kpsewhich','-var-value=TEXMFDIST'],work,env))
        trees=[dist];sibling=dist.parent.parent/'texmf'
        if sibling.is_dir():trees.append(sibling)
        env['TEXMF']='{'+','.join(map(str,trees))+'}'
        env['TEXFORMATS']=str(work)+os.pathsep
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
             '-halt-on-error','-jobname=pdflatex','pdflatex.ini'],work,env)
        maps=[]
        for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
            maps.append(Path(run(['kpsewhich',name],work,env)).read_bytes())
        (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous=None
    for j in range(6):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
             '-file-line-error','Report211.tex'],work,env)
        state=tuple((work/('Report211.'+s)).read_bytes() if (work/('Report211.'+s)).exists() else b''
                    for s in ('aux','toc','out'))
        if j and state==previous:break
        previous=state
    else:raise RuntimeError('TeX references failed to stabilize')
    log=(work/'Report211.log').read_text(errors='replace')
    defects=re.findall(r'(?:Overfull[^\n]*|Underfull[^\n]*|Missing character:[^\n]*|(?:LaTeX(?: Font)?|Package \S+) Warning[^\n]*)',log)
    if a.logs_dir:
        a.logs_dir.mkdir(parents=True)
        for suffix in ('log','aux','toc','out'):
            if (work/('Report211.'+suffix)).exists():
                shutil.copyfile(work/('Report211.'+suffix),a.logs_dir/('Report211.'+suffix))
    need(not defects,'TeX layout or reference defects: '+'; '.join(defects))
    data=(work/'Report211.pdf').read_bytes()
    need(data.startswith(b'%PDF-'),'PDF missing')
    with a.output.open('xb') as out:out.write(data)
print('PASS: built Report211 PDF')
