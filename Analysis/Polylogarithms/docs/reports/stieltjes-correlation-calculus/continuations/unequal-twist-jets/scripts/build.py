#!/usr/bin/env python3
"""Compile both PDFs in isolated temporary directories with pdfLaTeX.
A rebuild changes the published artifacts; rerun visual review and regenerate
SHA256SUMS deliberately rather than treating old receipts as current evidence.
"""
from __future__ import annotations
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main()->None:
    engine=shutil.which('pdflatex')
    if not engine:raise SystemExit('pdfLaTeX is required (TeX Live or MiKTeX).')
    logs=ROOT/'validation'/'build';logs.mkdir(parents=True,exist_ok=True)
    results=[]
    with tempfile.TemporaryDirectory(prefix='proveit_unequal_twist_') as temp:
        work=Path(temp)
        shutil.copy2(ROOT/'article.tex',work/'article.tex')
        (work/'integration').mkdir()
        for name in ('addendum-preview.tex','07-unequal-twist-jets.tex'):
            shutil.copy2(ROOT/'integration'/name,work/'integration'/name)
        for relative in ('article.tex','integration/addendum-preview.tex'):
            src=work/relative;output=[]
            for pass_no in range(1,4):
                run=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',src.name],cwd=src.parent,
                                   capture_output=True,text=True,timeout=180)
                output.append(f'=== pass {pass_no} ===\n'+run.stdout+run.stderr)
                if run.returncode:
                    (logs/(src.stem+'-console.txt')).write_text('\n'.join(output))
                    raise SystemExit(f'Compilation failed: {relative}; see validation/build.')
            text=src.with_suffix('.log').read_text(errors='replace')
            forbidden=['Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations']
            bad=[pattern for pattern in forbidden if pattern in text]
            if bad:raise SystemExit(f'Layout/reference review required for {relative}: {bad}')
            destination=ROOT/Path(relative).with_suffix('.pdf')
            shutil.copy2(src.with_suffix('.pdf'),destination)
            shutil.copy2(src.with_suffix('.log'),logs/(src.stem+'.log'))
            (logs/(src.stem+'-console.txt')).write_text('\n'.join(output))
            results.append({'source':relative,'pdf':str(destination.relative_to(ROOT)),
                            'pdf_sha256':hashlib.sha256(destination.read_bytes()).hexdigest(),
                            'passes':3,'no_overfull_boxes':True,'no_unresolved_references':True})
    (logs/'build-record.json').write_text(json.dumps({'engine':'pdfLaTeX','results':results,
              'visual_review_required_after_rebuild':True},indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
