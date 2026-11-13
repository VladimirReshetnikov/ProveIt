"""Compile the standalone LaTeX source in an otherwise empty directory."""
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parent
source = root / 'ipra_uniform_clauses.tex'
engine = shutil.which('pdflatex')
if engine is None:
    raise SystemExit('PDFLaTeX is required to rebuild the report.')
with tempfile.TemporaryDirectory(prefix='ipra_uniform_clauses_') as temporary:
    work = Path(temporary)
    shutil.copy2(source, work / source.name)
    for _ in range(2):
        result = subprocess.run(
            [engine, '-no-shell-escape', '-interaction=nonstopmode',
             '-halt-on-error', source.name],
            cwd=work, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
    shutil.copy2(work / source.with_suffix('.pdf').name,
                 source.with_suffix('.pdf'))
    (root / 'evidence').mkdir(exist_ok=True)
    shutil.copy2(work / source.with_suffix('.log').name,
                 root / 'evidence/latex_build.log')
print('Built ipra_uniform_clauses.pdf from the standalone TeX source.')
