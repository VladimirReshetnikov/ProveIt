#!/usr/bin/env python3
"""Regenerate the delivery manifest after an intentional artifact edit."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent.parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

files = []
for p in sorted(ROOT.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts or p.suffix == '.pyc':
        continue
    rel = p.relative_to(ROOT).as_posix()
    if rel in {'MANIFEST.json', 'SHA256SUMS'}:
        continue
    files.append({'path': rel, 'bytes': p.stat().st_size, 'sha256': sha(p)})
data = {'format': 'st215-delivery-manifest-v1',
        'excludes': ['MANIFEST.json', 'SHA256SUMS', '__pycache__/', '*.pyc'],
        'files': files}
(ROOT / 'MANIFEST.json').write_text(json.dumps(data, indent=2) + '\n')
paths = [ROOT / item['path'] for item in files] + [ROOT / 'MANIFEST.json']
(ROOT / 'SHA256SUMS').write_text(''.join(
    f'{sha(p)}  {p.relative_to(ROOT).as_posix()}\n' for p in sorted(paths)))
print(f'Manifest records {len(files)} files')
