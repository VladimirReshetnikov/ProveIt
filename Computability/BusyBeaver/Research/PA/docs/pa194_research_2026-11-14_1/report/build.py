#!/usr/bin/env python3
"""Build the report using installed TeX; isolate missing format/font setup.

The isolated-format method follows the build_report.py supplied with the
incoming PA194 witness packet. It does not alter system files or use network.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

def locate(name, env):
    p = subprocess.run(['kpsewhich', name], env=env, text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else ''

if not shutil.which('pdftex') or not shutil.which('kpsewhich'):
    raise SystemExit('Install a TeX distribution with pdfTeX and the report packages.')
subprocess.run(['python3', '-B', 'generate.py'], cwd=HERE, check=True)
env = os.environ.copy()
with tempfile.TemporaryDirectory(prefix='pa194-report-tex-') as temp:
    command = ['pdflatex']
    if not locate('pdflatex.fmt', env):
        roots = [p for p in ('/usr/share/texlive/texmf-dist', '/usr/share/texmf',
                             '/var/lib/texmf', '/etc/texmf') if Path(p).is_dir()]
        env['TEXMF'] = '{.,' + ','.join(roots) + '}'
        subprocess.run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                        '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex',
                        'pdflatex.ini'], cwd=temp, env=env, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        command = ['pdftex', '-fmt=' + str(Path(temp) / 'pdflatex.fmt'), '-progname=pdflatex']
    if not locate('pdftex.map', env):
        maps = [locate(name, env) for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map')]
        maps = [Path(p).read_text() for p in maps if p]
        if not maps:
            raise SystemExit('No scalable font maps were found.')
        (Path(temp) / 'pdftex.map').write_text('\n'.join(maps))
        env['TEXFONTMAPS'] = temp + os.pathsep + env.get('TEXFONTMAPS', '')
    for _ in range(3):
        p = subprocess.run(command + ['-interaction=nonstopmode', '-halt-on-error', 'report.tex'],
                           cwd=HERE, env=env, text=True, capture_output=True)
        if p.returncode:
            print(p.stdout[-12000:])
            raise SystemExit(p.returncode)
print(HERE / 'report.pdf')
