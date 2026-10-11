#!/usr/bin/env python3
"""Render every page and inspect extractable text geometry; no OCR is used.

Visual review of the rendered images is a separate manual/model step.
Render files are kept OUTSIDE the distribution directory by default.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import fitz

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--render-dir',type=Path,default=ROOT.parent/(ROOT.name+'_pdf_review'))
    parser.add_argument('--dpi',type=int,default=120)
    args=parser.parse_args()
    if args.dpi<72:parser.error('Use at least 72 dpi')
    args.render_dir.mkdir(parents=True,exist_ok=True)
    doc=fitz.open(ROOT/'article.pdf')
    issues=[];pages=[]
    for i,page in enumerate(doc):
        text=page.get_text()
        if not text.strip():issues.append({'page':i+1,'problem':'No extractable text'})
        if '\ufffd' in text or '\x00' in text:issues.append({'page':i+1,'problem':'Replacement/null character'})
        outside=[]
        for block in page.get_text('dict')['blocks']:
            for line in block.get('lines',[]):
                for span in line.get('spans',[]):
                    b=fitz.Rect(span['bbox'])
                    if b.x0 < -1 or b.y0 < -1 or b.x1 > page.rect.width+1 or b.y1 > page.rect.height+1:
                        outside.append(span['text'])
        if outside:issues.append({'page':i+1,'problem':'Text outside physical page','spans':outside})
        image=f'page_{i+1:02d}.png'
        page.get_pixmap(matrix=fitz.Matrix(args.dpi/72,args.dpi/72),alpha=False).save(args.render_dir/image)
        pages.append({'page':i+1,'text_characters':len(text),'render':image,'outside_text_spans':len(outside)})
    text='\n'.join(p.get_text() for p in doc)
    for required in ('Finite Lerch master','Single-anchor finite-closure criterion','Symbolic mixed-parity cancellation',
                     'Further research questions and proposed directions'):
        if required.lower() not in text.lower():issues.append({'problem':'Required heading missing','heading':required})
    receipt={'status':'PASS' if not issues else 'FAIL','pages':len(doc),'dpi':args.dpi,
             'renderer':'PyMuPDF '+fitz.VersionBind,'issues':issues,'page_details':pages,
             'visual_review':'Required separately; successful geometry checks do not replace visual inspection.'}
    (ROOT/'data'/'pdf_inspection.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='page_details'},indent=2))
    if issues:raise SystemExit(1)

if __name__=='__main__':main()
