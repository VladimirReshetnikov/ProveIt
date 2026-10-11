#!/usr/bin/env python3
"""Inspect PDF text geometry and optionally render every page for visual review.

Usage: python3 code/inspect_pdf.py --preview-dir /absolute/temporary/directory
Rendering requires pdftoppm (Poppler). Contact sheets use Pillow.
Geometry checks supplement human visual review; they do not prove legibility.
"""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import fitz

ROOT = Path(__file__).resolve().parents[1]
PDF = ROOT / 'Independent_Orders_and_Exact_Reductions.pdf'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--preview-dir', type=Path)
    args = parser.parse_args()
    document = fitz.open(PDF)
    records = []
    all_text = []
    for number, page in enumerate(document, 1):
        text = page.get_text()
        all_text.append(text)
        clipped = []
        outside_body_width = []
        for block in page.get_text('dict')['blocks']:
            for line in block.get('lines', []):
                for span in line['spans']:
                    x0,y0,x1,y1 = span['bbox']
                    if x0 < -0.5 or y0 < -0.5 or x1 > page.rect.width+0.5 or y1 > page.rect.height+0.5:
                        clipped.append({'text':span['text'], 'bbox':span['bbox']})
                    if x0 < 68 or x1 > page.rect.width-68:
                        outside_body_width.append({'text':span['text'], 'bbox':span['bbox']})
        records.append({'page':number, 'text_characters':len(text),
                        'clipped_spans':clipped, 'outside_body_width':outside_body_width,
                        'replacement_character': '\ufffd' in text,
                        'unresolved_reference_marker': '??' in text})
    report = {'schema':'proveit.pdf.geometry.v1', 'pdf':PDF.name,
              'pages':len(document), 'page_size_points':list(document[0].rect),
              'extracted_words':sum(len(t.split()) for t in all_text),
              'clipped_spans':sum(len(x['clipped_spans']) for x in records),
              'outside_body_width_spans':sum(len(x['outside_body_width']) for x in records),
              'replacement_character_pages':[x['page'] for x in records if x['replacement_character']],
              'unresolved_reference_pages':[x['page'] for x in records if x['unresolved_reference_marker']],
              'page_records':records,
              'qualification':'Automated geometry and extraction checks; visual review is recorded separately.'}
    (ROOT/'results/pdf_geometry.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='page_records'},indent=2))
    if args.preview_dir:
        from PIL import Image, ImageOps, ImageDraw
        if not shutil.which('pdftoppm'):
            raise SystemExit('Install Poppler to render the PDF.')
        destination=args.preview_dir.resolve()
        destination.mkdir(parents=True,exist_ok=True)
        subprocess.run(['pdftoppm','-scale-to','1400','-png',str(PDF),str(destination/'page')],check=True,
                       stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
        pages=sorted(destination.glob('page-*.png'))
        for start in range(0,len(pages),6):
            sheet=Image.new('RGB',(1120,2292),'#d8dce2')
            draw=ImageDraw.Draw(sheet)
            for j,path in enumerate(pages[start:start+6]):
                page=Image.open(path).convert('RGB')
                page.thumbnail((540,700))
                x=10+(j%2)*560; y=28+(j//2)*764
                sheet.paste(page,(x,y))
                draw.text((x,y-20),f'Page {start+j+1}',fill='black')
            sheet.save(destination/f'contact_{start+1:02d}_{min(start+6,len(pages)):02d}.png')
        print(f'Rendered {len(pages)} pages and contact sheets to {destination}')


if __name__=='__main__':
    main()
