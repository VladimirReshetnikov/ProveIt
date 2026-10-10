#!/usr/bin/env python3
"""Build the research article with pdfLaTeX; retain the final compiler log."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
STEM = 'integral_distribution'


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--keep-aux', action='store_true')
    args = ap.parse_args()
    engine = shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdfLaTeX was not found. Install a TeX distribution with the packages named in the article preamble.')
    folder = ROOT / 'article'
    (ROOT / 'logs').mkdir(exist_ok=True)
    for index in range(3):
        result = subprocess.run(
            [engine, '-interaction=nonstopmode', '-halt-on-error', '-file-line-error', STEM + '.tex'],
            cwd=folder, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            encoding='utf-8', errors='replace', check=False,
        )
        if result.returncode:
            (ROOT / 'logs' / 'latex_failure.txt').write_text(result.stdout, encoding='utf-8')
            raise SystemExit(f'pdfLaTeX failed on pass {index+1}; see logs/latex_failure.txt.')
    text = (folder / (STEM + '.log')).read_text(encoding='utf-8', errors='replace')
    (ROOT / 'logs' / 'latex_final.txt').write_text(text, encoding='utf-8')
    forbidden = ['Overfull \\hbox', 'Overfull \\vbox', 'There were undefined references',
                 'LaTeX Warning: Label(s) may have changed', 'multiply defined']
    found = [message for message in forbidden if message in text]
    if found:
        raise SystemExit('Build requires layout/reference review: ' + '; '.join(found))
    if not args.keep_aux:
        for suffix in ('.aux', '.log', '.toc', '.out', '.fls', '.fdb_latexmk', '.synctex.gz'):
            (folder / (STEM + suffix)).unlink(missing_ok=True)
    pdf = folder / (STEM + '.pdf')
    if not pdf.is_file() or not pdf.stat().st_size:
        raise SystemExit('The expected nonempty PDF was not produced.')
    print(f'Built {pdf.relative_to(ROOT)} ({pdf.stat().st_size:,} bytes).')
    print('No overfull boxes, undefined references, or unresolved label warnings in the final log.')


if __name__ == '__main__':
    main()
