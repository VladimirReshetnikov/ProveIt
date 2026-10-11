#!/usr/bin/env python3
"""Render the article for a fresh visual review; this script cannot certify a human review.

Usage: python code/inspect_pdf.py [--pdf path] [--output directory]
Dependencies: PyMuPDF, Pillow. Default images are written to build/pdf-review/.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import fitz
from PIL import Image, ImageDraw

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', type=Path, default=ROOT / 'article.pdf')
    parser.add_argument('--output', type=Path, default=ROOT / 'build' / 'pdf-review')
    args = parser.parse_args()
    if not args.pdf.is_file():
        raise SystemExit(f'PDF not found: {args.pdf}')
    args.output.mkdir(parents=True, exist_ok=True)
    doc = fitz.open(args.pdf)
    cards = []
    suspect = []
    for index, page in enumerate(doc):
        path = args.output / f'page-{index+1:02d}.png'
        page.get_pixmap(matrix=fitz.Matrix(1.35, 1.35), alpha=False).save(path)
        with Image.open(path) as opened:
            image = opened.copy()
        image.thumbnail((245, 320))
        card = Image.new('RGB', (265, 350), '#eeeeee')
        card.paste(image, ((265-image.width)//2, 10))
        ImageDraw.Draw(card).text((12, 332), f'Page {index+1}', fill='black')
        cards.append(card)
        for block in page.get_text('blocks'):
            if block[0] < 55 or block[2] > page.rect.width-55 or block[1] < 20 or block[3] > page.rect.height-17:
                suspect.append({'page': index+1, 'bbox': list(block[:4]), 'excerpt': block[4][:100]})
    cols = 5
    rows = (len(cards)+cols-1)//cols
    sheet = Image.new('RGB', (cols*265, rows*350), 'white')
    for index, card in enumerate(cards):
        sheet.paste(card, ((index % cols)*265, (index//cols)*350))
    sheet.save(args.output / 'contact-sheet.png')
    receipt = {'pdf': str(args.pdf), 'pages': len(doc), 'renderer': f'PyMuPDF {fitz.VersionBind}',
               'potential_out_of_bounds_blocks': suspect,
               'scope': 'Structural screen and rendered images only. Inspect the images before claiming visual review.'}
    (args.output / 'structural_check.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(f'Rendered {len(doc)} pages to {args.output}; potential out-of-bounds blocks: {len(suspect)}.')

if __name__ == '__main__':
    main()
