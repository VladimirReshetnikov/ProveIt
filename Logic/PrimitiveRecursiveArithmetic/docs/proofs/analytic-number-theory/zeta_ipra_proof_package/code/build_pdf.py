#!/usr/bin/env python3
"""Build the LaTeX PDF and record errors/warnings without shell escape."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

root=Path(__file__).resolve().parents[1]
build=root/'build'
build.mkdir(exist_ok=True)
source=root/'paper'/'zeta_ipra.tex'
env=os.environ.copy()
def kpse(name):
    r=subprocess.run(['kpsewhich',name],env=env,stdout=subprocess.PIPE,
                     stderr=subprocess.DEVNULL,text=True)
    return r.stdout.strip()
# Support a TeX tree whose generated filename database is absent.
if not kpse('article.cls') and Path('/usr/share/texlive/texmf-dist').is_dir():
    env['TEXMF']='{/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
if not kpse('pdflatex.fmt'):
    fmt=build/'texformat'
    fmt.mkdir(exist_ok=True)
    if not (fmt/'pdflatex.fmt').exists():
        result=subprocess.run(['pdftex','-ini','-etex','-interaction=nonstopmode',
            '-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],
            cwd=fmt,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (fmt/'format-build.txt').write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-4000:]); raise SystemExit(result.returncode)
    env['TEXFORMATS']=str(fmt)+os.pathsep
if not kpse('pdftex.map'):
    maps=build/'fontmaps'
    maps.mkdir(exist_ok=True)
    parts=[]
    for name in ['lm.map','cm.map','cmextra.map','symbols.map','latxfont.map']:
        path=kpse(name)
        if path:
            parts.append(Path(path).read_text(errors='replace'))
    if not parts:
        raise SystemExit('Required TeX font map files are unavailable.')
    (maps/'pdftex.map').write_text('\n'.join(parts))
    env['TEXFONTMAPS']=str(maps)+os.pathsep
for step in range(3):
    p=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                      '-file-line-error','-output-directory='+str(build),source.name],
                     cwd=source.parent,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (build/f'pass-{step+1}.txt').write_text(p.stdout)
    if p.returncode:
        print(p.stdout[-7000:])
        raise SystemExit(p.returncode)
log=(build/'zeta_ipra.log').read_text(errors='replace')
shutil.copy2(build/'zeta_ipra.pdf',root/'zeta_ipra.pdf')
report={'passes':3,'exit_code':0,
        'overfull_boxes':re.findall(r'Overfull[^\n]*(?:\n[^\n]*)?',log),
        'undefined_references':bool(re.search('undefined references|Citation .* undefined|Reference .* undefined',log)),
        'pdf_bytes':(root/'zeta_ipra.pdf').stat().st_size,
        'lean_checked':False}
(root/'verification'/'build.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
