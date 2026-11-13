#!/usr/bin/env python3
"""Rebuild the displayed PDF in a fresh temporary directory."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';TEX=BASE/'equation69-2011.tex';PDF=BASE/'equation69-2011.pdf'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='equation69-pdf-review-') as t:
    build=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+t,str(TEX.relative_to(ROOT))],cwd=ROOT,capture_output=True,text=True,timeout=60)
    if build.returncode:raise ValueError(('pdflatex failed',build.returncode,build.stdout[-4000:]))
    made=Path(t)/'equation69-2011.pdf'
    if sha(made)!=sha(PDF):raise ValueError('PDF bytes differ')
    info=subprocess.run(['pdfinfo',str(made)],capture_output=True,text=True,check=True).stdout
    if 'Pages:           1' not in info or 'Page size:       612 x 792 pts (letter)' not in info:raise ValueError('page count or size')
    out=subprocess.run(['pdftotext','-layout',str(made),'-'],capture_output=True,text=True,check=True).stdout
    if 'A thirteen-variable consistency equation' not in out or 'The integer' not in out or 'base 10' not in out:raise ValueError('missing rendered text')
    print(json.dumps({'status':'PASS_REPRODUCIBLE_ONE_PAGE_EQUATION69_PDF','pdf_sha256':sha(made),'pages':1,'size':'letter','build_exit':build.returncode,'font_size_substitution_warning':'size substitutions' in build.stdout.lower()},indent=2))
