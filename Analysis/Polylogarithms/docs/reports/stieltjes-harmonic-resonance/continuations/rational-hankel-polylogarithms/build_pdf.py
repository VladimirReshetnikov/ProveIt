"""Build the self-contained article with pdflatex; stop on TeX errors."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent
if shutil.which('pdflatex') is None:
    raise SystemExit('pdflatex was not found. Install a TeX distribution and retry.')
for n in range(1, 4):
    proc = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                           '-halt-on-error', 'article.tex'], cwd=root,
                          text=True, capture_output=True, check=False)
    (root / 'data' / f'pdf_build_pass_{n}.txt').write_text(
        proc.stdout + proc.stderr, encoding='utf-8')
    if proc.returncode:
        print(proc.stdout[-5000:])
        raise SystemExit(proc.returncode)
print(root / 'article.pdf')
