from pathlib import Path
import hashlib,json
import fitz
B=Path(__file__).resolve().parents[1];R=B.parents[3];out=R/'tmp/polylog-eleventh-review'
previous=out/'previous';rows=[]
for pdf in sorted((B/'volumes').glob('*.pdf')):
    old=fitz.open(previous/pdf.name);new=fitz.open(pdf)
    def h(page):return hashlib.sha256(page.get_pixmap(matrix=fitz.Matrix(.38,.38),alpha=False).samples).hexdigest()
    identical=[i+1 for i in range(min(len(old),len(new))) if h(old[i])==h(new[i])]
    changed=[i+1 for i in range(len(new)) if i+1 not in identical]
    row=dict(pdf=pdf.name,old_pdf_sha256=hashlib.sha256((previous/pdf.name).read_bytes()).hexdigest(),pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),page_count=len(new),same_index_identical_pages=identical,changed_pages=changed)
    rows.append(row)
    print(pdf.name,'pages',len(new),'identical',len(identical),'changed',changed)
    folder=out/pdf.stem;folder.mkdir(exist_ok=True)
    full=set(changed) if 'volume-1' not in pdf.stem else set(range(55,60))|{len(new)}
    for n in sorted(full):
        new[n-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False).save(folder/f'page-{n:03}.png')
    row['full_pages_rendered']=sorted(full)
(B/'verification/eleventh-volume-raster-comparison.json').write_text(json.dumps(dict(volumes=rows,scope='Exact same-index page-raster comparison with the preceding manually reviewed PDFs. Changed Volume I is reviewed in full contact sheets and new proof pages; unchanged other-volume rasters retain that prior review, with changed bibliography pages reviewed freshly.'),indent=2)+'\n')
