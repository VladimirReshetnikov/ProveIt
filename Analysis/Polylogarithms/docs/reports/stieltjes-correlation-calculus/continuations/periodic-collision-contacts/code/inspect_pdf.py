#!/usr/bin/env python3
"""Render the compiled article and record basic structural checks.

Images are placed outside the delivery directory by default. Rendering and
structural checks do not constitute an independent mathematical review.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import fitz
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[1]
STEM = 'Periodic_Stieltjes_Collisions'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--render-directory', type=Path, default=ROOT.parent / '_periodic_collision_review')
    parser.add_argument('--dpi', type=int, default=120)
    args = parser.parse_args()
    if not 60 <= args.dpi <= 400:
        parser.error('--dpi must lie between 60 and 400')
    pdf = ROOT / f'{STEM}.pdf'
    if not pdf.is_file():
        raise SystemExit('Build the PDF first with python code/build.py.')
    args.render_directory.mkdir(parents=True, exist_ok=True)
    document = fitz.open(pdf)
    pages = []
    images = []
    all_text = ''
    for index, page in enumerate(document):
        text = page.get_text()
        all_text += text
        pixmap = page.get_pixmap(matrix=fitz.Matrix(args.dpi/72, args.dpi/72), alpha=False)
        destination = args.render_directory / f'page-{index+1:02d}.png'
        pixmap.save(destination)
        images.append(destination)
        outside = []
        for block in page.get_text('dict')['blocks']:
            if block['type'] != 0:
                continue
            for line in block['lines']:
                for span in line['spans']:
                    rect = fitz.Rect(span['bbox'])
                    if not (page.rect + (-1,-1,1,1)).contains(rect):
                        outside.append(span['text'])
        pages.append({'page':index+1, 'text_characters':len(text), 'outside_page_text':outside})
    width = 300
    thumb_height = 448
    for start in range(0, len(images), 9):
        subset = images[start:start+9]
        sheet = Image.new('RGB', (3*width, 3*thumb_height), 'white')
        draw = ImageDraw.Draw(sheet)
        for j, path in enumerate(subset):
            image = Image.open(path)
            image.thumbnail((width-12, thumb_height-25))
            x, y = (j%3)*width, (j//3)*thumb_height
            sheet.paste(image, (x+(width-image.width)//2,y+20))
            draw.text((x+8,y+3), f'Page {start+j+1}', fill='black')
        sheet.save(args.render_directory / f'contact-sheet-{start//9+1}.png')
    source = (ROOT / f'{STEM}.tex').read_text()
    labels = re.findall(r'\\label\{([^}]+)\}', source)
    references = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', source)
    checks = {
        'all_pages_have_text': all(p['text_characters'] > 100 for p in pages),
        'no_text_outside_page': all(not p['outside_page_text'] for p in pages),
        'no_unresolved_question_marks': '??' not in all_text,
        'no_replacement_characters': '\ufffd' not in all_text,
        'unique_source_labels': len(labels) == len(set(labels)),
        'all_source_references_defined': all(ref in labels for ref in references)
    }
    receipt = {
        'status':'passed' if all(checks.values()) else 'needs inspection',
        'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),
        'page_count':len(document), 'renderer':f'PyMuPDF {fitz.VersionBind}',
        'render_dpi':args.dpi, 'checks':checks, 'pages':pages,
        'note':'Automated structural checks and rendered images only. Visual and mathematical reviews have separate scopes.'
    }
    (ROOT / 'data' / 'pdf_inspection.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (args.render_directory / 'extracted_text.txt').write_text(all_text)
    print(json.dumps({k:v for k,v in receipt.items() if k!='pages'},indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
