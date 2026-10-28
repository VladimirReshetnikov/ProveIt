#!/usr/bin/env python3
"""Build the LaTeX research report using an isolated temporary directory."""
from __future__ import annotations
import os, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]

def main():
    source = ROOT/'report'
    if not shutil.which('pdflatex'):
        raise RuntimeError('pdfLaTeX is required; install a standard TeX distribution.')
    env = dict(os.environ)
    env['SOURCE_DATE_EPOCH'] = '1793055600'
    env['FORCE_SOURCE_DATE'] = '1'
    with tempfile.TemporaryDirectory(prefix='latex-build-', dir=source) as work:
        work = Path(work)
        for item in source.glob('*.tex'):
            shutil.copy2(item,work/item.name)
        for _ in range(3):
            p = subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                                '-halt-on-error','report.tex'], cwd=work, env=env,
                               text=True,capture_output=True)
            if p.returncode:
                raise RuntimeError(p.stdout[-12000:]+'\n'+p.stderr)
        log=(work/'report.log').read_text(errors='replace')
        warnings=[line for line in log.splitlines()
                  if 'Overfull' in line or 'undefined' in line or 'LaTeX Warning' in line]
        shutil.copy2(work/'report.pdf',source/'report.pdf')
        (ROOT/'results/report_build.log').write_text(log)
        print('Built report/report.pdf')
        if warnings:print('\n'.join(warnings))

if __name__=='__main__':main()
