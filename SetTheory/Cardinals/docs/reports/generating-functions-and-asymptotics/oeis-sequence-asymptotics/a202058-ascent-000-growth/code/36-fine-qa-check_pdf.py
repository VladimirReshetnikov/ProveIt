#!/usr/bin/env python3
"""Structural PDF checks; every rendered page additionally requires visual inspection."""
from pathlib import Path
import hashlib,json,subprocess
import fitz
ROOT=Path(__file__).resolve().parents[1]
PDF=ROOT/'a202058-fine-addendum.pdf'
QA=ROOT/'qa'; QA.mkdir(exist_ok=True)
doc=fitz.open(PDF)
text='\n'.join(p.get_text() for p in doc)
(QA/'extracted-text.txt').write_text(text)
issues=[]
for j,page in enumerate(doc,1):
    for block in page.get_text('blocks'):
        x0,y0,x1,y1,body,*_=block
        if not str(body).strip():continue
        if x0<35 or x1>page.rect.width-35 or y0<30 or y1>page.rect.height-25:
            issues.append({'page':j,'bbox':[x0,y0,x1,y1],'text':str(body)[:180]})
assert '\ufffd' not in text,'Replacement glyph in extracted PDF text'
assert '??' not in text,'Potential unresolved reference in PDF text'
subprocess.run(['pdftoppm','-r','130','-png',str(PDF),str(QA/'page')],check=True)
result={'pdf_sha256':hashlib.sha256(PDF.read_bytes()).hexdigest(),'pages':len(doc),'page_sizes_points':[[p.rect.width,p.rect.height] for p in doc],'text_bbox_warnings':issues,'rendering_dpi':130,'visual_review':'pending','note':'Geometry and text checks do not replace visual review of all page PNGs.'}
(QA/'structural-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
