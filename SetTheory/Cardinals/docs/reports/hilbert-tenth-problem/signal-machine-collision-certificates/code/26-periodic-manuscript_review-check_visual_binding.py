#!/usr/bin/env python3
"""Bind independently rendered PNGs and the visually inspected pages to final PDF."""
import json
import hashlib
from pathlib import Path
import subprocess
from PIL import Image, ImageChops

if not __debug__:
    raise SystemExit('Assertions must remain enabled')

base = Path('/workspace/shared/report56-independent-manuscript-review-20261004')
release = Path('/workspace/shared/periodic-signal-report56-release-20261004')
old = Path('/workspace/shared/report56-render-d-20261004')
new = Path('/workspace/shared/report56-render-e-20261004')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

tex = release/'article/Report56.tex'
pdf = release/'article/Report56.pdf'
assert sha(tex) == '8c5f54158e5ca70cc7d92497ee6fb6d32fb1e49d9a03b8aed14e0498e88642b6'
assert sha(pdf) == '4853f8c578f42b7273d693199ce768f8b68c95fa8ee64433f959b122751136ea'
before_edit = tex.read_bytes().replace(b'the normalized values over a full period', b'the values over a full period')
assert hashlib.sha256(before_edit).hexdigest() == 'c737fd7bc362d3891af4c24100455d729f682691ecd6595ad4464f5e96fff3d0'
info = subprocess.run(['pdfinfo',str(pdf)],check=True,capture_output=True,text=True).stdout
assert 'Pages:           15' in info
pages = []
changed = []
for i in range(1,16):
    name = f'page-{i:02}.png'
    initial = base/'initial-pdf-render'/name
    final = base/'final-pdf-render'/name
    assert sha(initial) == sha(old/name)
    a,b = Image.open(final),Image.open(new/name)
    assert a.size == b.size == (978,1265)
    assert ImageChops.difference(a,b).getbbox() is None
    if sha(old/name) != sha(new/name):
        changed.append(i)
    pages.append({'page':i,'sha256':sha(final),'size':[978,1265],
                  'directly_visually_reviewed':True,'independent_final_pdf_render_matches':True})
assert changed == [5]
copies = {}
for dirname, original in [('science','substrate-semantics56-20261004'),
                           ('independent_audit','periodic-signal-independent-audit-20261004')]:
    src = Path('/workspace/shared')/original
    files = sorted(p.relative_to(src) for p in src.rglob('*') if p.is_file())
    targets = sorted(p.relative_to(release/dirname) for p in (release/dirname).rglob('*') if p.is_file())
    assert files == targets
    for name in files:
        assert (src/name).read_bytes() == (release/dirname/name).read_bytes()
        assert (src/name).stat().st_mode == (release/dirname/name).stat().st_mode
    copies[dirname] = len(files)
print(json.dumps({'status':'PASS','source_sha256':sha(tex),'pdf_sha256':sha(pdf),
    'source_delta':'Only added normalized to the full-period values sentence',
    'changed_pages_from_initial_review':changed,'pages':pages,
    'frozen_packet_file_counts_verified_byte_and_mode_equal':copies,
    'render_command':'pdftoppm -r 115 -png FINAL_PDF FINAL_OUTPUT_PREFIX',
    'visual_review':'All 15 original pages directly inspected; final page 5 separately directly inspected; other 14 final pages byte-identical to inspected originals'},indent=2,sort_keys=True))
