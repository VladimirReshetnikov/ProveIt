#!/usr/bin/env python3
"""Compile the LaTeX report; use an isolated format if TeX is unconfigured.

Requires installed pdfTeX and the packages listed in report.tex.  Uses only
local installed TeX sources and fonts; never downloads or changes system files.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

folder = Path(__file__).resolve().parent


def locate(name, environment):
    r = subprocess.run(['kpsewhich', name], env=environment,
                       text=True, capture_output=True)
    return r.stdout.strip() if r.returncode == 0 else ''


if not shutil.which('pdftex') or not shutil.which('kpsewhich'):
    raise SystemExit('Install TeX Live with pdfTeX and the report preamble packages.')
environment = os.environ.copy()
with tempfile.TemporaryDirectory(prefix='pa194-witness-tex-') as temporary:
    command = ['pdflatex']
    if not locate('pdflatex.fmt', environment):
        roots = [p for p in ('/usr/share/texlive/texmf-dist', '/usr/share/texmf',
                            '/var/lib/texmf', '/etc/texmf') if Path(p).is_dir()]
        if roots:
            environment['TEXMF'] = '{.,' + ','.join(roots) + '}'
        subprocess.run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                        '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex',
                        'pdflatex.ini'], cwd=temporary, env=environment, check=True)
        command = ['pdftex', '-fmt=' + str(Path(temporary) / 'pdflatex.fmt'),
                   '-progname=pdflatex']
    if not locate('pdftex.map', environment):
        fontmaps = []
        for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
            path = locate(name, environment)
            if path:
                fontmaps.append(Path(path).read_text())
        if not fontmaps:
            raise SystemExit('No installed scalable font maps found.')
        (Path(temporary) / 'pdftex.map').write_text('\n'.join(fontmaps))
        environment['TEXFONTMAPS'] = temporary + os.pathsep + environment.get('TEXFONTMAPS', '')
    command += ['-interaction=nonstopmode', '-halt-on-error', 'report.tex']
    for _ in range(3):
        subprocess.run(command, cwd=folder, env=environment, check=True)
print(folder / 'report.pdf')
