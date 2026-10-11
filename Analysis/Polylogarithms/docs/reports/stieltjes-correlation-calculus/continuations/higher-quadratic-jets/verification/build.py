#!/usr/bin/env python3
"""Assemble the self-contained TeX and build the PDF with three serial passes."""
from pathlib import Path
import argparse, shutil, subprocess, sys
ROOT=Path(__file__).resolve().parents[1]
NAME='ProveIt_Higher_Quadratic_Jets_2026-10-11'
def main(assemble_only=False):
    chunks=[(ROOT/'preamble.tex').read_text()]
    for f in sorted((ROOT/'sections').glob('*.tex')):
        chunks.extend([f'\n% BEGIN {f.relative_to(ROOT)}\n',f.read_text(),f'\n% END {f.relative_to(ROOT)}\n'])
    chunks.append((ROOT/'references.tex').read_text())
    tex=ROOT/(NAME+'.tex');tex.write_text(''.join(chunks))
    if assemble_only:
        print(tex);return
    engine=shutil.which('pdflatex') or shutil.which('lualatex')
    if not engine: raise SystemExit('Install pdflatex or lualatex to build the PDF.')
    for run in range(3):
        proc=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',tex.name],cwd=ROOT,
                            stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (ROOT/'data'/f'build_pass_{run+1}.txt').write_text(proc.stdout)
        if proc.returncode:
            print(proc.stdout[-12000:]);raise SystemExit(proc.returncode)
    print(ROOT/(NAME+'.pdf'))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--assemble-only',action='store_true')
    main(ap.parse_args().assemble_only)
