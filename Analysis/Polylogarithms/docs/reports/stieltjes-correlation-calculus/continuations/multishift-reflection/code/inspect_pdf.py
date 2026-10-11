#!/usr/bin/env python3
"""Render every article page outside the distribution; collect layout diagnostics.

Bounding-box checks are a screen for clipping, not a substitute for visual review.
"""
import argparse,json
from pathlib import Path
import fitz
from PIL import Image,ImageOps,ImageDraw
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT.parent/(ROOT.name+'_renders'));args=p.parse_args()
args.output.mkdir(parents=True,exist_ok=True)
doc=fitz.open(ROOT/'article.pdf');bad=[];images=[];pages=[]
for i,page in enumerate(doc):
    text=page.get_text()
    if not text.strip() or '\ufffd' in text: bad.append({'page':i+1,'problem':'empty page or replacement character'})
    for b in page.get_text('blocks'):
        if b[0]<30 or b[2]>page.rect.width-30 or b[1]<15 or b[3]>page.rect.height-15:
            bad.append({'page':i+1,'problem':'text near physical edge','bbox':list(b[:4])})
    path=args.output/f'page-{i+1:02}.png'
    page.get_pixmap(matrix=fitz.Matrix(1.6,1.6),alpha=False).save(path)
    im=Image.open(path);im.thumbnail((290,390))
    tile=Image.new('RGB',(310,420),'white');tile.paste(im,((310-im.width)//2,10))
    ImageDraw.Draw(tile).text((10,405),f'Page {i+1}',fill='black');images.append(tile)
    pages.append({'page':i+1,'text_characters':len(text),'render':str(path)})
cols=4;rows=(len(images)+cols-1)//cols
sheet=Image.new('RGB',(cols*310,rows*420),'#cccccc')
for i,tile in enumerate(images):sheet.paste(tile,((i%cols)*310,(i//cols)*420))
sheet.save(args.output/'contact-sheet.png')
receipt={'pages':len(doc),'automated_layout_flags':bad,'page_records':pages,
         'visual_review':'Separate manual review is recorded in visual_review.md.'}
(ROOT/'data/pdf_inspection.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'pages':len(doc),'layout_flags':bad,'contact_sheet':str(args.output/'contact-sheet.png')},indent=2))
if bad:raise SystemExit(1)
