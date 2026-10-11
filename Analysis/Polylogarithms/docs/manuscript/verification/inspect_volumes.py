"""Inspect all volume pages, chapter coverage and linked PDF destinations."""
from pathlib import Path
from collections import Counter
import hashlib,json,re
import fitz
from PIL import Image,ImageDraw

B=Path(__file__).resolve().parents[1];V=B/'verification'
plan=json.loads((V/'volume-plan.json').read_text(encoding='utf-8'))
render=B.parents[3]/'tmp/polylog-universal-euler-review/volumes-final'
docs={x['stem']+'.pdf':fitz.open(B/'volumes'/(x['stem']+'.pdf')) for x in plan}
destinations={name:doc.resolve_names() for name,doc in docs.items()}
all_issues=[];records=[]
master=(B/'polylogarithms.tex').read_text(encoding='utf-8')
roots=re.findall(r'\\input\{chapters/([^}]+)\}',master)
assigned=[name for x in plan for _,name in x['chapters']]+['11-literature']
coverage=Counter(assigned)==Counter(roots) and all(n==1 for n in Counter(assigned).values())
if not coverage:all_issues.append(dict(kind='chapter-partition',expected=roots,assigned=assigned))
for volume in plan:
    name=volume['stem']+'.pdf';doc=docs[name];out=render/('volume-'+str(volume['number']))
    out.mkdir(parents=True,exist_ok=True);issues=[];links=[];full={1,2,3,len(doc)}
    if doc.metadata.get('author')!='ProveIt Contributors':issues.append(dict(kind='author'))
    for n,page in enumerate(doc):
        text=page.get_text()
        if '??' in text:issues.append(dict(page=n+1,kind='unresolved-reference'))
        if 'Chapter ' in text[:200]:full.update({n+1,min(n+2,len(doc))})
        if any(s in text for s in ['A quarter-Gamma evaluation','Finite reduction at every',
            'real branch on both sides','Twisted Lerch family','Exact zero-mode renormalization']):full.add(n+1)
        for block in page.get_text('dict')['blocks']:
            for line in block.get('lines',[]):
                for span in line['spans']:
                    r=fitz.Rect(span['bbox'])
                    if r.x0<-.5 or r.y0<-.5 or r.x1>page.rect.width+.5 or r.y1>page.rect.height+.5:
                        issues.append(dict(page=n+1,kind='text-outside-page',text=span['text']))
        for link in page.get_links():
            if not link.get('file'):continue
            annotation=link['xref']
            action=doc.xref_get_key(annotation,'A/S')
            filetype,target=doc.xref_get_key(annotation,'A/F')
            desttype,dest=doc.xref_get_key(annotation,'A/D')
            valid=action==('name','/GoToR') and filetype=='string' and target in docs
            if valid and desttype=='string':valid=dest in destinations[target]
            elif valid and desttype=='array':valid=bool(re.match(r'\[\s*0\s*/Fit\s*\]',dest))
            else:valid=False
            row=dict(page=n+1,target=target,destination=dest,destination_type=desttype,passed=valid)
            links.append(row)
            if not valid:issues.append(dict(kind='external-PDF-destination',**row))
        pix=page.get_pixmap(matrix=fitz.Matrix(.38,.38),alpha=False)
        Image.frombytes('RGB',[pix.width,pix.height],pix.samples).save(out/f'thumb-{n+1:03}.png')
    for first in range(0,len(doc),16):
        sheet=Image.new('RGB',(1000,1440),'#dedede');draw=ImageDraw.Draw(sheet)
        for j in range(16):
            n=first+j
            if n>=len(doc):break
            im=Image.open(out/f'thumb-{n+1:03}.png')
            xx=(j%4)*250+(250-im.width)//2;yy=(j//4)*360+22
            sheet.paste(im,(xx,yy));draw.text(((j%4)*250+10,(j//4)*360+5),f'Volume {volume["number"]}, page {n+1}',fill='black')
        sheet.save(out/f'contact-{first+1:03}.png')
    for n in sorted(full):doc[n-1].get_pixmap(matrix=fitz.Matrix(1.35,1.35),alpha=False).save(out/f'page-{n:03}.png')
    record=dict(number=volume['number'],title=volume['title'],pdf='volumes/'+name,
        page_count=len(doc),pdf_author=doc.metadata.get('author'),
        pdf_sha256=hashlib.sha256((B/'volumes'/name).read_bytes()).hexdigest(),
        external_links=links,render_directory=str(out),contact_sheets=(len(doc)+15)//16,
        full_pages=sorted(full),issues=issues,passed=not issues)
    records.append(record);all_issues.extend(issues)
result=dict(passed=coverage and not all_issues,chapter_partition_complete=coverage,
    chapter_roots=assigned,volumes=records,total_pages=sum(x['page_count'] for x in records),
    external_destinations_verified=sum(len(x['external_links']) for x in records),issues=all_issues,
    scope='All pages inspected for text/reference/bounds, every external PDF destination verified, every original chapter assigned once. Raster generation is separate from human visual review.')
(V/'volume-inspection.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='volumes'},indent=2))
for x in records:print(x['number'],x['page_count'],'pages;',len(x['external_links']),'verified PDF links')
raise SystemExit(0 if result['passed'] else 1)
