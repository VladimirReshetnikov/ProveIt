#!/usr/bin/env python3
"""Verify all files recorded in the release manifest."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'MANIFEST.sha256.json').read_text())
for item in manifest['files']:
    path=root/item['path']
    if not path.is_file():raise RuntimeError('Missing release file: '+item['path'])
    value=hashlib.sha256(path.read_bytes()).hexdigest()
    if value!=item['sha256']:raise RuntimeError('Changed release file: '+item['path'])
print('Verified '+str(len(manifest['files']))+' release files.')
