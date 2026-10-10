#!/usr/bin/env python3
"""Compile the article in an isolated directory; keep no TeX scratch files."""
from __future__ import annotations
from pathlib import Path
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'article'/'beta_transfer.tex'
EPOCH=int(dt.datetime(2026,10,10,5,16,49,tzinfo=dt.timezone.utc).timestamp())

def main() -> None:
    executable=shutil.which('pdflatex')
    if executable is None:
        raise SystemExit('pdflatex is required; install a TeX distribution with the packages named in the source.')
    env=os.environ.copy()
    env.update(SOURCE_DATE_EPOCH=str(EPOCH),FORCE_SOURCE_DATE='1',TZ='UTC')
    with tempfile.TemporaryDirectory(prefix='proveit-beta-transfer-') as scratch:
        final_log=''
        for _ in range(3):
            result=subprocess.run([executable,'-interaction=nonstopmode','-halt-on-error',
                                   '-output-directory',scratch,str(SOURCE)],
                                  cwd=SOURCE.parent,env=env,text=True,
                                  stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)
            if result.returncode:
                raise SystemExit(result.stdout)
            final_log=result.stdout
        log_path=Path(scratch)/'beta_transfer.log'
        texlog=log_path.read_text(errors='replace')
        bad=[line for line in texlog.splitlines() if
             ('Overfull' in line or 'undefined references' in line or
              'Undefined control sequence' in line or 'Label(s) may have changed' in line)]
        if bad:
            raise SystemExit('Unresolved build issue:\n'+'\n'.join(bad))
        target=ROOT/'article'/'beta_transfer.pdf'
        shutil.copyfile(Path(scratch)/'beta_transfer.pdf',target)
        normalized_log=texlog.replace(scratch,'<isolated-build>').replace(str(ROOT),'<report>')
        (ROOT/'data'/'latex_build.log').write_text(normalized_log)
    pages=None
    if shutil.which('pdfinfo'):
        info=subprocess.check_output(['pdfinfo',str(target)],text=True)
        match=re.search(r'^Pages:\s+(\d+)',info,re.M)
        pages=int(match.group(1)) if match else None
    version=subprocess.check_output([executable,'--version'],text=True).splitlines()[0]
    receipt={'status':'PASS','passes':3,'pages':pages,'compiler':version,
             'source_date_epoch':EPOCH,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
             'pdf_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
             'overfull_boxes':0,'undefined_references':0,'build_directory':'isolated temporary directory'}
    (ROOT/'data'/'build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(f'PASS three-pass PDF build: {pages} pages; no overfull boxes or undefined references')

if __name__=='__main__':main()
