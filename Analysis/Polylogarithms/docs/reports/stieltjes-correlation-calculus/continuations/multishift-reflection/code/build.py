#!/usr/bin/env python3
"""Compile the self-contained article and reject common broken-build states."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
engine=shutil.which('pdflatex')
if not engine: raise SystemExit('pdflatex is required (a standard TeX Live installation suffices).')
work=ROOT/'build';work.mkdir(exist_ok=True)
for i in range(3):
 result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error',
                        '-output-directory',str(work),'article.tex'],cwd=ROOT,
                       stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (work/f'pass{i+1}.txt').write_text(result.stdout)
 if result.returncode: raise SystemExit(result.stdout[-6000:])
log=(work/'article.log').read_text(errors='replace')
patterns=[r'LaTeX Warning: Reference .* undefined',r'LaTeX Warning: Citation .* undefined',
          r'There were undefined references',r'Overfull \\[hv]box']
problems=[p for p in patterns if re.search(p,log)]
if problems: raise SystemExit('Build needs review: '+str(problems))
shutil.copyfile(work/'article.pdf',ROOT/'article.pdf')
receipt={'engine':subprocess.run([engine,'--version'],capture_output=True,text=True).stdout.splitlines()[0],
         'passes':3,'undefined_references':False,'overfull_boxes':False,
         'pdf_sha256':hashlib.sha256((ROOT/'article.pdf').read_bytes()).hexdigest()}
(ROOT/'data/build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
