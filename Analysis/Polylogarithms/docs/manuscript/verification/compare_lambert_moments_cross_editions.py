"""Match changed combined bodies to freshly reviewed current volume pages.
Only centered footer page numbers are excluded, with all other bounds audited.
This records raster equivalence; human review is recorded separately.
"""
from pathlib import Path
import hashlib,json,re
import fitz
B=Path(__file__).resolve().parents[1];V=B/'verification'
def body_hash(page):
    cut=page.rect.height-57
    excluded=[s for b in page.get_text('dict')['blocks'] for line in b.get('lines',[]) for s in line['spans'] if s['bbox'][3]>cut]
    assert all(not s['text'].strip() or (re.fullmatch(r'[0-9ivxlcdm]+',s['text']) and s['bbox'][1]>=cut and abs((s['bbox'][0]+s['bbox'][2])/2-page.rect.width/2)<20) for s in excluded),(page.number+1,excluded)
    assert all(x['bbox'][3]<=cut for x in page.get_image_info()),page.number+1
    assert all(x['rect'].y1<=cut for x in page.get_drawings()),page.number+1
    return hashlib.sha256(page.get_pixmap(matrix=fitz.Matrix(.38,.38),clip=fitz.Rect(0,0,page.rect.width,cut),alpha=False).samples).hexdigest()
r=json.loads((V/'lambert-moments-raster-comparison.json').read_text());c=r['pdfs'][-1];known={}
for number,x in enumerate(r['pdfs'][:4],1):
    path=B/'volumes'/x['pdf'];assert hashlib.sha256(path.read_bytes()).hexdigest()==x['pdf_sha256'];doc=fitz.open(path)
    for n in x['changed_scientific_bodies']:known[body_hash(doc[n-1])]=dict(volume_number=number,reviewed_volume_page=n,pdf_sha256=x['pdf_sha256'])
path=B/'polylogarithms.pdf';assert hashlib.sha256(path.read_bytes()).hexdigest()==c['pdf_sha256'];d=fitz.open(path);matched=[];fresh=[]
for n in c['changed_scientific_bodies']:
    key=body_hash(d[n-1])
    if key in known:matched.append(dict(combined_page=n,**known[key]))
    else:fresh.append(n)
out=dict(combined_pdf_sha256=c['pdf_sha256'],exact_matching_reviewed_bodies=matched,remaining_full_pages_to_review=fresh,crop_bottom_points=57,excluded_content_is_only_centered_footer_page_numbers=True)
(V/'lambert-moments-cross-edition-review.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print('Exact fresh-review matches:',len(matched),'remaining full pages:',fresh)
