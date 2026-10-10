"""PDF text/bounds audit plus contact sheets for a separate human visual review."""
from pathlib import Path
import argparse, hashlib, json
import fitz
from PIL import Image, ImageDraw

B=Path(__file__).resolve().parents[1]
pdf=B/'polylogarithms.pdf'
parser=argparse.ArgumentParser()
parser.add_argument('--render-directory',type=Path,default=B.parents[3]/'tmp/polylog-review')
parser.add_argument('--full-pages',type=int,nargs='*',default=[])
args=parser.parse_args()
out=args.render_directory.resolve()
out.mkdir(parents=True,exist_ok=True)
doc=fitz.open(pdf)
issues=[]; pages=[]
for n,page in enumerate(doc):
    txt=page.get_text()
    if '??' in txt:issues.append(dict(page=n+1,kind='unresolved-reference-text'))
    for block in page.get_text('dict')['blocks']:
        for line in block.get('lines',[]):
            for span in line['spans']:
                r=fitz.Rect(span['bbox'])
                if r.x0<-0.5 or r.y0<-0.5 or r.x1>page.rect.width+0.5 or r.y1>page.rect.height+0.5:
                    issues.append(dict(page=n+1,kind='text-outside-page',text=span['text'],bbox=list(r)))
    pages.append(dict(page=n+1,text_characters=len(txt),chapter_start=('Chapter ' in txt[:200]),
                      sha256=hashlib.sha256(txt.encode()).hexdigest()))
    pix=page.get_pixmap(matrix=fitz.Matrix(0.38,0.38),alpha=False)
    im=Image.frombytes('RGB',[pix.width,pix.height],pix.samples)
    im.save(out/f'thumb-{n+1:03}.png')
for first in range(0,len(doc),16):
    sheet=Image.new('RGB',(1000,1440),'#dedede');draw=ImageDraw.Draw(sheet)
    for j in range(16):
        n=first+j
        if n>=len(doc):break
        im=Image.open(out/f'thumb-{n+1:03}.png')
        x=(j%4)*250+(250-im.width)//2;y=(j//4)*360+22
        sheet.paste(im,(x,y));draw.text(((j%4)*250+10,(j//4)*360+5),'PDF page '+str(n+1),fill='black')
    sheet.save(out/f'contact-{first+1:03}.png')
selected={1,2,3,4,5,6,len(doc),*args.full_pages}
for n,page in enumerate(doc):
    txt=page.get_text()
    if 'Chapter ' in txt[:200]:selected.update({n+1,min(n+2,len(doc))})
    if any(t in txt for t in ('Odd-denominator harmonic','fifth antiderivative','2814912','98820','third and quarter values','Cohen')):selected.add(n+1)
for n in sorted(selected):
    pix=doc[n-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False)
    pix.save(out/f'page-{n:03}.png')
record=dict(pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),page_count=len(doc),issues=issues,
            raster_directory=str(out),rendered_contact_sheets=(len(doc)+15)//16,
            full_pages=sorted(selected),pages=pages,static_passed=not issues)
(B/'verification/pdf-inspection.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='pages'},indent=2))
raise SystemExit(0 if record['static_passed'] else 1)
