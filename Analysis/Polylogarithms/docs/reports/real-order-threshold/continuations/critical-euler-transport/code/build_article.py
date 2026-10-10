#!/usr/bin/env python3
"""Compile the self-contained TeX article in a temporary build directory."""
from __future__ import annotations
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'article'/'critical_euler_transport.tex'

def main() -> None:
    latex=shutil.which('pdflatex')
    if latex is None:
        raise SystemExit('pdflatex is required to compile this article.')
    with tempfile.TemporaryDirectory(prefix='critical-euler-build-') as tmp:
        out=Path(tmp)
        for _ in range(3):
            command=[latex,'-interaction=nonstopmode','-halt-on-error',
                     f'-output-directory={out}',str(SOURCE)]
            proc=subprocess.run(command,cwd=SOURCE.parent,text=True,
                                stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                                timeout=120)
            if proc.returncode:
                raise SystemExit(proc.stdout[-12000:])
        log=(out/(SOURCE.stem+'.log')).read_text(errors='replace')
        forbidden=['Overfull \\hbox','Overfull \\vbox','undefined references',
                   'undefined citations','Label(s) may have changed']
        problems=[x for x in forbidden if x in log]
        if problems:
            raise SystemExit('Build requires review: '+', '.join(problems))
        pdf=SOURCE.with_suffix('.pdf')
        shutil.copyfile(out/pdf.name,pdf)
        match=re.search(r'Output written on .*?\((\d+) pages',log,re.S)
        receipt={'status':'PASS','source':str(SOURCE.relative_to(ROOT)),
                 'pdf':str(pdf.relative_to(ROOT)),'passes':3,
                 'pages':int(match.group(1)) if match else None,
                 'pdf_bytes':pdf.stat().st_size,
                 'overfull_boxes':False,'unresolved_references':False,
                 'note':'Render inspection is recorded separately; compilation is not proof verification.'}
        (ROOT/'data'/'build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
