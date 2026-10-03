#!/usr/bin/env python3
"""Build the standalone LaTeX report; also supports minimally indexed TeX Live installations."""
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
BUILD.mkdir(exist_ok=True)
env = os.environ.copy()
env['TEXMFVAR'] = str(BUILD / 'texmf-var')
env['TEXMFCONFIG'] = str(BUILD / 'texmf-config')
# These conventional, public system trees are fallbacks, not bundle dependencies.
roots = [Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')]
roots = [p for p in roots if p.exists()]
if roots:
    env['TEXINPUTS'] = str(ROOT) + os.pathsep + os.pathsep.join(str(p / 'tex') + '//' for p in roots) + os.pathsep
    env['TEXFONTS'] = os.pathsep.join(str(p / 'fonts') + '//' for p in roots) + os.pathsep
    env['TEXFORMATS'] = str(BUILD) + '//' + os.pathsep
    env['TEXFONTMAPS'] = str(BUILD) + os.pathsep + os.pathsep.join(str(p / 'fonts' / 'map') + '//' for p in roots) + os.pathsep
    maps = []
    for p in roots:
        for relative in ['fonts/map/dvips/lm/lm.map', 'fonts/map/dvips/amsfonts/cm.map',
                         'fonts/map/dvips/amsfonts/cmextra.map', 'fonts/map/dvips/amsfonts/symbols.map']:
            f = p / relative
            if f.exists(): maps.append(f)
    if maps:
        (BUILD / 'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
    if not (BUILD / 'pdflatex.fmt').exists():
        with (BUILD / 'format-build.log').open('w') as log:
            subprocess.run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode', '-halt-on-error',
                            '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                           cwd=BUILD, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
for i in range(3):
    with (BUILD / ('latex-pass-' + str(i + 1) + '.log')).open('w') as log:
        subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                        '-output-directory=' + str(BUILD), 'eager-tree-certificates.tex'],
                       cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
shutil.copy2(BUILD / 'eager-tree-certificates.pdf', ROOT / 'eager-tree-certificates.pdf')
print('Built eager-tree-certificates.pdf')
