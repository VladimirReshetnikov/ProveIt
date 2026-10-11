#!/usr/bin/env python3
"""Flatten the TeX source and compile the modular article three times."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
def flatten(path: Path) -> str:
    text=path.read_text()
    def expand(match):
        part=match.group(1)
        target=ROOT/(part if part.endswith('.tex') else part+'.tex')
        if not target.is_file():raise FileNotFoundError(target)
        return '% BEGIN '+str(target.relative_to(ROOT))+'\n'+flatten(target)+'\n% END '+part+'\n'
    return re.sub(r'\\input\{([^}]+)\}',expand,text)

(ROOT/'article_standalone.tex').write_text(flatten(ROOT/'article.tex'))
engine=shutil.which('pdflatex')
if engine is None:raise SystemExit('pdflatex is required; install a TeX distribution.')
(ROOT/'verification').mkdir(exist_ok=True)
with (ROOT/'verification'/'latex_build.log').open('w') as log:
    for _ in range(3):
        subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','article.tex'],
                       cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
print('Built article.pdf and article_standalone.tex')
