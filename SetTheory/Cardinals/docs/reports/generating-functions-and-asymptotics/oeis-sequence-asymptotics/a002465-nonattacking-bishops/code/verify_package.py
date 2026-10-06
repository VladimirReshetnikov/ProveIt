#!/usr/bin/env python3
"""Check every file in the extracted Report219 package against its manifest."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
if manifest.get('schema_version') != 1 or manifest.get('report') != 'Report219':
    raise ValueError('Unrecognized package manifest')
for name, expected in manifest['files'].items():
    relative = Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('Unsafe manifest path')
    path = root/relative
    if not path.is_file() or path.is_symlink():
        raise ValueError('Missing or non-ordinary package file: '+name)
    data = path.read_bytes()
    if len(data) != expected['bytes'] or hashlib.sha256(data).hexdigest() != expected['sha256']:
        raise ValueError('Integrity mismatch: '+name)
print('PASS: '+str(len(manifest['files']))+' manifest entries verified')
