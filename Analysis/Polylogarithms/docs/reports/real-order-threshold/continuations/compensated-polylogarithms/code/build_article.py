#!/usr/bin/env python3
"""Build the standalone article with pdflatex, without leaving auxiliary files."""
from __future__ import annotations
import re, shutil, subprocess, tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    executable = shutil.which('pdflatex')
    if executable is None:
        raise SystemExit('pdflatex is required. Install a LaTeX distribution with the packages used in article.tex.')
    with tempfile.TemporaryDirectory(prefix='proveit-polylog-') as temp:
        work=Path(temp)
        shutil.copy2(ROOT/'article.tex',work/'article.tex')
        for _ in range(3):
            proc=subprocess.run([executable,'-interaction=nonstopmode','-halt-on-error','article.tex'],
                                cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            if proc.returncode:
                raise SystemExit(proc.stdout[-15000:])
        log=(work/'article.log').read_text(errors='replace')
        bad=[line for line in log.splitlines() if any(x in line for x in
             ['Overfull', 'undefined references', 'undefined citations', 'Label(s) may have changed'])]
        if bad:
            raise SystemExit('LaTeX validation failed:\n'+'\n'.join(bad))
        shutil.copy2(work/'article.pdf',ROOT/'article.pdf')
        match=re.search(r'Output written on article.pdf \((\d+) pages',log)
        print('Built article.pdf'+(f' ({match.group(1)} pages)' if match else ''))

if __name__=='__main__':
    main()
