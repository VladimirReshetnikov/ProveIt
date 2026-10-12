#!/usr/bin/env python3
"""Build the self-contained LaTeX article without leaving TeX auxiliaries."""
from pathlib import Path
import shutil, subprocess, tempfile
ROOT=Path(__file__).resolve().parent
engine=shutil.which('pdflatex')
if engine is None:
    raise SystemExit('pdflatex is required. Install a TeX distribution with the packages used by article.tex.')
with tempfile.TemporaryDirectory(prefix='proveit_vertical_lattice_') as tmp:
    logs=[]
    for i in range(3):
        proc=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',
                             f'-output-directory={tmp}',str(ROOT/'article.tex')],
                            cwd=ROOT,capture_output=True,text=True,timeout=120)
        logs.append(f'=== PASS {i+1} ===\n'+proc.stdout+proc.stderr)
        if proc.returncode:
            (ROOT/'results'/'build.log').write_text('\n'.join(logs))
            raise SystemExit('LaTeX failed; see results/build.log.')
    final_log=(Path(tmp)/'article.log').read_text(errors='replace')
    failures=[line for line in final_log.splitlines() if
              'Overfull' in line or ('undefined' in line.lower() and 'Warning' in line)]
    (ROOT/'results'/'build.log').write_text('\n'.join(logs))
    if failures:
        raise SystemExit('Layout/reference check failed:\n'+'\n'.join(failures))
    shutil.copy2(Path(tmp)/'article.pdf',ROOT/'article.pdf')
print('Built article.pdf; three passes; no overfull boxes or undefined-reference warnings.')
