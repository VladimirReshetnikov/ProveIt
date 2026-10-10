#!/usr/bin/env python3
"""Build the article with three serial PDFLaTeX passes (cross-platform)."""
from pathlib import Path
import shutil,subprocess

root=Path(__file__).resolve().parents[1]
engine=shutil.which('pdflatex')
if engine is None:raise SystemExit('pdflatex not found; install TeX Live or MiKTeX with the packages used by the article.')
(root/'logs').mkdir(exist_ok=True)
for n in range(1,4):
    result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','cayley_s4.tex'],
                          cwd=root/'article',capture_output=True,text=True,check=False)
    (root/'logs'/f'latex_pass{n}.txt').write_text(result.stdout+result.stderr)
    if result.returncode:raise SystemExit(f'LaTeX pass {n} failed; see logs/latex_pass{n}.txt')
print(root/'article/cayley_s4.pdf')
print('A changed PDF needs its own rendered review; the original visual-review receipt applies only to its recorded hash.')
