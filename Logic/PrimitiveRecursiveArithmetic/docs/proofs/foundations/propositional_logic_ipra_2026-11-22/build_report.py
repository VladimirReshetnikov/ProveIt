#!/usr/bin/env python3
"""Build the report with pdfLaTeX, including a local fallback for stripped TeX installs.

No network access is used. On a normal TeX installation only three pdfLaTeX
passes are needed. Generated formats/maps remain inside build/.
"""
from pathlib import Path
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
BUILD.mkdir(exist_ok=True)
env = os.environ.copy()
distribution = Path('/usr/share/texlive/texmf-dist')

def lookup(name):
    if not shutil.which('kpsewhich'):
        return ''
    result = subprocess.run(['kpsewhich', name], env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    return result.stdout.strip()

if not lookup('article.cls') and distribution.is_dir():
    # Some container images retain the distribution but omit its ls-R database.
    env['TEXMF'] = str(distribution)

pdflatex = shutil.which('pdflatex')
if not pdflatex:
    raise SystemExit('pdfLaTeX is required; install a TeX distribution with AMS packages.')

fmt = lookup('pdflatex.fmt')
extra_args = []
if not fmt:
    local_fmt = BUILD / 'pdflatex.fmt'
    if not local_fmt.exists():
        pdftex = shutil.which('pdftex')
        if not pdftex or not lookup('pdflatex.ini'):
            raise SystemExit('No pdfLaTeX format or local format-building sources are available.')
        with (BUILD / 'format-build.log').open('w') as log:
            subprocess.run([pdftex, '-ini', '-etex', '-jobname=pdflatex',
                            '-progname=pdflatex', '-interaction=nonstopmode',
                            '-halt-on-error', 'pdflatex.ini'], cwd=BUILD,
                           env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    extra_args = ['-fmt=' + str(local_fmt)]

if not lookup('pdftex.map'):
    map_sources = [lookup(n) for n in ('cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map')]
    if not all(map_sources):
        raise SystemExit('Computer Modern/AMS Type 1 font maps are missing.')
    (BUILD / 'pdftex.map').write_text('\n'.join(Path(n).read_text() for n in map_sources))
    env['TEXFONTMAPS'] = str(BUILD) + os.pathsep + env.get('TEXFONTMAPS', '')

command = [pdflatex, *extra_args, '-interaction=nonstopmode', '-halt-on-error',
           '-file-line-error', '-jobname=propositional_logic_ipra',
           '-output-directory=' + str(BUILD), 'report.tex']
for number in range(1, 4):
    log_path = BUILD / f'latex-pass-{number}.txt'
    with log_path.open('w') as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        print(log_path.read_text()[-8000:])
        raise SystemExit(f'LaTeX pass {number} failed; see {log_path}')

destination = ROOT / 'propositional_logic_ipra.pdf'
shutil.copyfile(BUILD / destination.name, destination)
print(destination)
