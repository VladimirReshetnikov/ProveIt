#!/usr/bin/env python3
"""Build the article using a standard TeX installation (cross-platform)."""
from __future__ import annotations
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def run(args: list[str]) -> None:
    proc = subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT,text=True,errors='replace')
    if proc.returncode:
        raise RuntimeError('Build command failed: '+' '.join(args)+'\n'+proc.stdout[-16000:])

def main() -> None:
    latex=shutil.which('pdflatex')
    if not latex:
        raise SystemExit('pdflatex was not found. Install TeX Live or MiKTeX, then retry.')
    command=[latex,'-interaction=nonstopmode','-halt-on-error','article.tex']
    run(command)
    bib=shutil.which('bibtex') or shutil.which('bibtex.original')
    if bib:
        run([bib,'article'])
    elif not (ROOT/'article.bbl').exists():
        raise SystemExit('BibTeX is missing, and there is no prebuilt article.bbl.')
    else:
        print('BibTeX unavailable: using the supplied article.bbl. Changes to references.bib require BibTeX.')
    for _ in range(3):
        run(command)
        log=(ROOT/'article.log').read_text(errors='replace')
        if 'Rerun to get cross-references right' not in log and 'undefined references' not in log:
            break
    log=(ROOT/'article.log').read_text(errors='replace')
    issues=[term for term in ('Overfull \\hbox','undefined references','undefined citations') if term in log]
    if issues:
        raise RuntimeError('PDF was produced, but review article.log: '+', '.join(issues))
    print('Built:',ROOT/'article.pdf')

if __name__=='__main__':main()
