#!/usr/bin/env python3
"""Read-only layout evidence for the final Report 53 PDF using local Poppler.
Visual inspection of every rendered page is separate and remains required.
"""
import sys
if not sys.flags.isolated or sys.flags.optimize:raise SystemExit('Use python3 -I without -O')
from pathlib import Path
import hashlib,json,subprocess,xml.etree.ElementTree as ET
root=Path(__file__).resolve().parent.parent
pdf=root/'Research_Report53.pdf'
result=subprocess.run(['pdftotext','-bbox',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=60)
# Poppler can emit control-code text for extensible math glyphs.
# Remove only XML-forbidden controls for parsing; bounding boxes are untouched.
controls=sum(ord(c)<32 and c not in '\t\n\r' for c in result.stdout)
clean=''.join(c for c in result.stdout if ord(c)>=32 or c in '\t\n\r')
doc=ET.fromstring(clean)
ns={'x':'http://www.w3.org/1999/xhtml'}
pages=doc.findall('.//x:page',ns)
assert len(pages)==17
bounds=[]
for index,page in enumerate(pages,1):
    width=float(page.attrib['width']);height=float(page.attrib['height']);words=page.findall('.//x:word',ns)
    assert words
    for word in words:
        a=word.attrib
        assert 0<=float(a['xMin'])<=float(a['xMax'])<=width
        assert 0<=float(a['yMin'])<=float(a['yMax'])<=height
        assert float(a['xMin'])>=60 and float(a['xMax'])<=width-60
    bounds.append({'page':index,'words':len(words),'x_min':min(float(w.attrib['xMin']) for w in words),'x_max':max(float(w.attrib['xMax']) for w in words),'y_min':min(float(w.attrib['yMin']) for w in words),'y_max':max(float(w.attrib['yMax']) for w in words)})
print(json.dumps({'status':'PASS','pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pages':len(pages),'xml_forbidden_extracted_math_controls_removed_for_parsing':controls,'all_word_boxes_inside_media':True,'all_word_boxes_within_60pt_horizontal_margin':True,'scope':'Machine-readable bounding-box check, not a replacement for visual or mathematical review','page_bounds':bounds},sort_keys=True,indent=2))
