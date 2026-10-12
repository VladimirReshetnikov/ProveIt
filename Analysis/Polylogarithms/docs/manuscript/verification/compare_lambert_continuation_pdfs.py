"""Compare final PDFs with the reviewed 1cd65680c3 publication.
Missing baseline PDFs are recovered read-only from that exact Git tree.
Raster agreement and human visual review have separate evidence scopes.
"""
from pathlib import Path
import hashlib,json,re,subprocess
import fitz
B=Path(__file__).resolve().parents[1];V=B/'verification';R=B.parents[3]
out=R/'tmp/polylog-beta-crossing-review/lambert-continuation';previous=R/'tmp/polylog-beta-crossing-review/lambert-continuation-previous'
rows=[]
def full_hash(page):return hashlib.sha256(page.get_pixmap(matrix=fitz.Matrix(.38,.38),alpha=False).samples).hexdigest()
def body_hash(page):
    cut=page.rect.height-57
    excluded=[s for b in page.get_text('dict')['blocks'] for line in b.get('lines',[]) for s in line['spans'] if s['bbox'][3]>cut]
    assert all(not s['text'].strip() or (re.fullmatch(r'[0-9ivxlcdm]+',s['text']) and s['bbox'][1]>=cut and abs((s['bbox'][0]+s['bbox'][2])/2-page.rect.width/2)<20) for s in excluded),(page.number+1,excluded)
    assert all(x['bbox'][3]<=cut for x in page.get_image_info()),page.number+1
    assert all(x['rect'].y1<=cut for x in page.get_drawings()),page.number+1
    return hashlib.sha256(page.get_pixmap(matrix=fitz.Matrix(.38,.38),clip=fitz.Rect(0,0,page.rect.width,cut),alpha=False).samples).hexdigest()
for pdf in [*sorted((B/'volumes').glob('*.pdf')),B/'polylogarithms.pdf']:
    baseline=previous/pdf.name
    if not baseline.is_file():
        previous.mkdir(parents=True,exist_ok=True)
        baseline.write_bytes(subprocess.check_output(['git','show','1cd65680c3378bfdf60fe18015b74af278781dee:'+pdf.relative_to(R).as_posix()],cwd=R))
    old=fitz.open(previous/pdf.name);new=fitz.open(pdf)
    old_bodies={body_hash(p):i+1 for i,p in enumerate(old)}
    same=[];matches=[];changed=[]
    for i,page in enumerate(new):
        if i<len(old) and full_hash(page)==full_hash(old[i]):same.append(i+1)
        key=body_hash(page)
        if key in old_bodies:matches.append(dict(page=i+1,previous_page=old_bodies[key]))
        else:changed.append(i+1)
    folder=out/pdf.stem;folder.mkdir(parents=True,exist_ok=True)
    # Full unchanged page rasters suffice for the bibliography-only volumes.
    full_pages=changed
    for n in full_pages:new[n-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False).save(folder/f'page-{n:03}.png')
    row=dict(pdf=pdf.name,pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),previous_pdf_sha256=hashlib.sha256((previous/pdf.name).read_bytes()).hexdigest(),page_count=len(new),same_index_full_raster_matches=same,exact_matching_scientific_bodies=matches,changed_scientific_bodies=changed,
      changed_contact_sheets=sorted({1+16*((n-1)//16) for n in changed}),full_pages_rendered=full_pages)
    rows.append(row);print(pdf.name,len(new),'pages; full same-index',len(same),'scientific bodies',len(matches),'changed',changed,flush=True)
record=dict(baseline_commit='1cd65680c3378bfdf60fe18015b74af278781dee',crop_bottom_points=57,excluded_content_is_only_centered_footer_page_numbers=True,pdfs=rows,
 scope='Exact full page rasters at the same index, and exact scientific page-body rasters allowing shifted indices. Only centered footer page numbers are excluded from body matching; text/image/drawing bounds ensure no scientific content is omitted. These comparisons retain prior visual review for matching content; newly changed pages are inspected separately.')
(V/'lambert-continuation-raster-comparison.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
