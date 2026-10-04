#!/usr/bin/env python3
"""New read-only PDF layout/data check. Does not run science or TeX code."""
import hashlib
import json
import sys
from pathlib import Path
import pdfplumber
from pypdf import PdfReader

def require(value, message):
    if not value:
        raise RuntimeError(message)

pdf = Path(sys.argv[1])
data = pdf.read_bytes()
rows = []
with pdfplumber.open(pdf) as book:
    require(len(book.pages) == 15, 'Expected 15 pages')
    for index, page in enumerate(book.pages, 1):
        require((float(page.width),float(page.height)) == (612.0,792.0),'Non-Letter page')
        chars = [c for c in page.chars if c.get('text','').strip()]
        require(len(chars)>200, 'Sparse or missing text page')
        require(all(0<=c['x0']<=c['x1']<=612.5 and 0<=c['top']<=c['bottom']<=792.5 for c in chars), 'Text outside media box')
        rows.append({'page':index,'visible_characters':len(chars),'text_inside_media_box':True})
reader=PdfReader(pdf)
require(not reader.is_encrypted,'Unexpected encryption')
require('/AcroForm' not in reader.trailer['/Root'],'Unexpected form')
links=[]
for number,page in enumerate(reader.pages,1):
    for ref in page.get('/Annots',[]):
        item=ref.get_object(); action=item.get('/A')
        if action and action.get('/URI'):
            uri=str(action['/URI']);require(uri.startswith('https://'),'Non-HTTPS external URI')
            links.append({'page':number,'uri':uri})
require(len(links)==5,'Unexpected external source-link count')
print(json.dumps({'status':'PASS','pdf_sha256':hashlib.sha256(data).hexdigest(),'pages':rows,'external_links':links,'scope':'Read-only page size, nonempty text, media-box bounds, and link metadata; visual review is separate'},sort_keys=True,indent=2))
