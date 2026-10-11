from pathlib import Path
import hashlib,json,re
import fitz
B=Path(__file__).resolve().parents[1];R=B.parents[3];out=R/'tmp/polylog-eleventh-review/combined'
previous=R/'tmp/polylog-eleventh-review/previous/polylogarithms.pdf'
old=fitz.open(previous);new=fitz.open(B/'polylogarithms.pdf')
def cropped(page):
    cut=page.rect.height-57
    excluded=[s for b in page.get_text('dict')['blocks'] for line in b.get('lines',[]) for s in line['spans'] if s['bbox'][3]>cut]
    assert all(not s['text'].strip() or (re.fullmatch(r'[0-9ivxlcdm]+',s['text']) and s['bbox'][1]>=cut and abs((s['bbox'][0]+s['bbox'][2])/2-page.rect.width/2)<20) for s in excluded),(page.number+1,excluded)
    assert all(x['bbox'][3]<=cut for x in page.get_image_info()),page.number+1
    assert all(x['rect'].y1<=cut for x in page.get_drawings()),page.number+1
    pix=page.get_pixmap(matrix=fitz.Matrix(.38,.38),clip=fitz.Rect(0,0,page.rect.width,cut),alpha=False)
    return hashlib.sha256(pix.samples).hexdigest()
byhash={cropped(p):i+1 for i,p in enumerate(old)}
matches=[];changed=[]
for i,p in enumerate(new):
    key=cropped(p)
    if key in byhash:matches.append(dict(page=i+1,previous_page=byhash[key]))
    else:changed.append(i+1)
for n in changed:
    new[n-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False).save(out/f'page-{n:03}.png')
record=dict(pdf_sha256=hashlib.sha256((B/'polylogarithms.pdf').read_bytes()).hexdigest(),previous_pdf_sha256=hashlib.sha256(previous.read_bytes()).hexdigest(),page_count=len(new),
  crop_bottom_points=57,excluded_content_is_only_page_numbers=True,exact_matching_page_bodies=matches,changed_page_bodies=changed,
  changed_contact_sheets=sorted({1+16*((n-1)//16) for n in changed}),
  scope='Exact cropped scientific page-body raster comparison with the prior reviewed combined PDF, allowing shifted page indices. Only footer page numbers are excluded: text, image and drawing bounds verify no mathematical content is removed. Static full-page inspection remains separate; every unmatched page is reviewed freshly.')
(B/'verification/eleventh-combined-raster-comparison.json').write_text(json.dumps(record,indent=2)+'\n')
print('Exactly matching scientific page bodies',len(matches),'fresh changed pages',changed,'sheets',record['changed_contact_sheets'])
