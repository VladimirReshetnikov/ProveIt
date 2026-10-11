#!/usr/bin/env python3
"""Build the standalone article; optionally regenerate all verification evidence."""
from __future__ import annotations
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent

def run(command: list[str]) -> None:
    print('+',' '.join(command),flush=True)
    subprocess.run(command,cwd=ROOT,check=True)

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true',help='run exact and numerical suites before compiling')
    args=parser.parse_args()
    engine=shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdflatex was not found. Install a LaTeX distribution with the packages listed in README.md.')
    if args.verify:
        run([sys.executable,'code/verify_exact.py'])
        run([sys.executable,'code/verify_numeric.py','--group','all','--dps','50'])
    data=ROOT/'data/harmonic_table.tex'
    if data.exists():
        source=ROOT/'article.tex'; text=source.read_text(encoding='utf-8')
        block='% BEGIN GENERATED HARMONIC TABLE\n'+data.read_text(encoding='utf-8').rstrip()+'\n% END GENERATED HARMONIC TABLE'
        text,count=re.subn(r'% BEGIN GENERATED HARMONIC TABLE.*?% END GENERATED HARMONIC TABLE',lambda match:block,text,flags=re.S)
        if count!=1: raise SystemExit('Expected exactly one generated harmonic-table block in article.tex.')
        source.write_text(text,encoding='utf-8')
    for _ in range(3):
        run([engine,'-interaction=nonstopmode','-halt-on-error','article.tex'])
    log=(ROOT/'article.log').read_text(errors='replace')
    if re.search(r'(LaTeX Warning: (?:Reference|Citation).*undefined|There were undefined references)',log):
        raise SystemExit('The PDF built with unresolved cross-references; inspect article.log.')
    output=ROOT/'article.pdf'
    if not output.is_file() or output.stat().st_size==0:
        raise SystemExit('Compilation did not produce a nonempty article.pdf.')
    print('Built',output)

if __name__=='__main__':
    try: main()
    except subprocess.CalledProcessError as exc:
        raise SystemExit(f'Command failed with exit status {exc.returncode}.') from exc
