"""Compile the standalone report with pdfLaTeX; no network is used."""
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
name = 'ipra_local_introduction.tex'
environment = os.environ.copy()
found = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, text=True)
if found.returncode != 0 or not found.stdout.strip():
    formats = ROOT / '.build'
    formats.mkdir(exist_ok=True)
    if not (formats / 'pdflatex.fmt').is_file():
        subprocess.run(['pdftex', '-ini', '-interaction=nonstopmode', '-halt-on-error',
                        '-jobname=pdflatex', '-progname=pdflatex', '-etex', 'pdflatex.ini'],
                       cwd=formats, check=True)
    environment['TEXFORMATS'] = str(formats) + os.pathsep + environment.get('TEXFORMATS', '')
for pass_number in range(3):
    subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                    '-file-line-error', name], cwd=ROOT, env=environment, check=True)
print(ROOT / 'ipra_local_introduction.pdf')
