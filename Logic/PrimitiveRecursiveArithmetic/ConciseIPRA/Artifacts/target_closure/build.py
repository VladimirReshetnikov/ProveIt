"""Regenerate standalone LaTeX sources and compile the two documents."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent


def flatten(source):
    def include(match):
        name = match.group(1)
        return '\n% BEGIN ' + name + '\n' + flatten((ROOT / name).read_text()) + '\n% END ' + name + '\n'
    return re.sub(r'\\input\{([^}]+)\}', include, source)


for name in ('report', 'foundations'):
    source = flatten((ROOT / (name + '_main.tex')).read_text())
    (ROOT / (name + '.tex')).write_text(source)
    for _ in range(2):
        subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', name + '.tex'], cwd=ROOT, check=True)
