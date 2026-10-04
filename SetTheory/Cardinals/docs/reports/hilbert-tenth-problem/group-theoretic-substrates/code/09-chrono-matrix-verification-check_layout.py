#!/usr/bin/env python3
"""Read-only bounding-box evidence for Report55. Visual review remains separate."""
import sys
if not sys.flags.isolated or sys.flags.optimize: raise SystemExit('Use python3 -I without -O')
from pathlib import Path
import hashlib,json,subprocess,xml.etree.ElementTree as ET

def require(ok,message):
    if not ok: raise RuntimeError(message)
root=Path(__file__).resolve().parent.parent
pdf=root/'article/Report55.pdf'
result=subprocess.run(['pdftotext','-bbox',str(pdf),'-'],capture_output=True,text=True,check=True,timeout=60)
controls=sum(ord(c)<32 and c not in '\t\n\r' for c in result.stdout)
clean=''.join(c for c in result.stdout if ord(c)>=32 or c in '\t\n\r')
doc=ET.fromstring(clean);ns={'x':'http://www.w3.org/1999/xhtml'}
pages=doc.findall('.//x:page',ns)
require(len(pages)==21,'Unexpected final page count')
bounds=[]
for index,page in enumerate(pages,1):
    width=float(page.attrib['width']);height=float(page.attrib['height']);words=page.findall('.//x:word',ns)
    require(bool(words),'Empty page')
    for word in words:
        a=word.attrib
        require(0<=float(a['xMin'])<=float(a['xMax'])<=width,'Horizontal crop')
        require(0<=float(a['yMin'])<=float(a['yMax'])<=height,'Vertical crop')
        require(float(a['xMin'])>=60 and float(a['xMax'])<=width-60,'Horizontal safe margin')
    bounds.append({'page':index,'words':len(words),'x_min':min(float(w.attrib['xMin']) for w in words),'x_max':max(float(w.attrib['xMax']) for w in words),'y_min':min(float(w.attrib['yMin']) for w in words),'y_max':max(float(w.attrib['yMax']) for w in words)})
print(json.dumps({'status':'PASS','pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pages':len(pages),'xml_forbidden_extracted_math_controls_removed_for_parsing':controls,'all_word_boxes_inside_media':True,'all_word_boxes_within_60pt_horizontal_margin':True,'scope':'Bounding-box evidence only, not a replacement for full-page visual or mathematical review','page_bounds':bounds},sort_keys=True,indent=2))
