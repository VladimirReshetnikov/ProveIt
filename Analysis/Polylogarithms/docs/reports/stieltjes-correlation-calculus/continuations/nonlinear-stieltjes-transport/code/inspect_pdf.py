#!/usr/bin/env python3
"""Static page-boundary checks plus temporary PNG rendering for visual review.
Requires Poppler. Static checks do not replace mathematical or visual review.
"""
import json,shutil,subprocess,tempfile
from pathlib import Path
import xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[1]
def main():
    for cmd in ['pdftotext','pdftoppm','pdfinfo']:
        if not shutil.which(cmd): raise SystemExit(f'Required Poppler tool is missing: {cmd}')
    with tempfile.TemporaryDirectory(prefix='nonlinear-pdf-review-') as tmp:
        tmp=Path(tmp)
        subprocess.run(['pdftotext','-bbox',str(ROOT/'article.pdf'),str(tmp/'bbox.html')],check=True)
        raw=(tmp/'bbox.html').read_text()
        # Poppler can emit form-feed/control characters in extracted math text.
        clean=''.join(c for c in raw if ord(c)>=32 or c in '\t\n\r')
        tree=ET.fromstring(clean); ns={'h':'http://www.w3.org/1999/xhtml'}
        pages=tree.findall('.//h:page',ns); outside=[]; counts=[]
        for i,page in enumerate(pages,1):
            W,H=float(page.attrib['width']),float(page.attrib['height']); words=page.findall('h:word',ns); counts.append(len(words))
            for word in words:
                a=word.attrib
                if float(a['xMin'])<-0.2 or float(a['yMin'])<-0.2 or float(a['xMax'])>W+.2 or float(a['yMax'])>H+.2:
                    outside.append({'page':i,'word':word.text,'box':a})
        if outside: raise SystemExit('Text outside page bounds: '+str(outside))
        subprocess.run(['pdftoppm','-scale-to','1000','-png',str(ROOT/'article.pdf'),str(tmp/'page')],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        receipt={'passed':True,'page_count':len(pages),'words_per_page':counts,'out_of_page_words':outside,'rendered_pages':len(list(tmp.glob('page-*.png'))),'rendering':'Poppler, temporary page PNGs','visual_review':'Separate human/model review recorded in data/visual_review.json.'}
        (ROOT/'data/pdf_inspection.json').write_text(json.dumps(receipt,indent=2)); print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
