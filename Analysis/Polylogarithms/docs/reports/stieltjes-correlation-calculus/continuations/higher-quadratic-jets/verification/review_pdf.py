#!/usr/bin/env python3
"""Render and mechanically inspect a PDF; human visual review is separate."""
from pathlib import Path
import argparse,hashlib,json
import fitz
ROOT=Path(__file__).resolve().parents[1]
NAME='ProveIt_Higher_Quadratic_Jets_2026-10-11.pdf'
def main(render_directory,output,dpi):
    pdf=ROOT/NAME;doc=fitz.open(pdf);bad=[];pages=[]
    if render_directory: render_directory.mkdir(parents=True,exist_ok=True)
    for n,page in enumerate(doc,1):
        text=page.get_text()
        if '\ufffd' in text or '??' in text: bad.append({'page':n,'issue':'replacement glyph or unresolved reference'})
        for word in page.get_text('words'):
            if word[0]<-1 or word[1]<-1 or word[2]>page.rect.width+1 or word[3]>page.rect.height+1:
                bad.append({'page':n,'issue':'text outside page rectangle','word':word[4]})
        pages.append({'page':n,'word_count':len(text.split()),'width_pt':page.rect.width,'height_pt':page.rect.height})
        if render_directory:
            page.get_pixmap(matrix=fitz.Matrix(dpi/72,dpi/72)).save(render_directory/f'page-{n:02d}.png')
    result={'pdf':NAME,'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'pages':len(doc),
            'renderer':'PyMuPDF '+fitz.VersionBind,'dpi':dpi,'page_checks':pages,'issues':bad,
            'status':'passed' if not bad else 'issues found','visual_review':'Not inferred by this script. Inspect the rendered pages separately.'}
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'{len(doc)} pages; {len(bad)} mechanical issues; output: {output}')
    if bad: raise SystemExit(1)
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--render-directory',type=Path)
    ap.add_argument('--output',type=Path,default=ROOT/'data'/'pdf_check.json');ap.add_argument('--dpi',type=int,default=144)
    a=ap.parse_args();main(a.render_directory,a.output,a.dpi)
