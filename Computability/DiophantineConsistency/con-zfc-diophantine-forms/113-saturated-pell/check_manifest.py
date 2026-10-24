#!/usr/bin/env python3
"""Verify the release files listed in MANIFEST.json; ignore local build outputs."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root/'MANIFEST.json').read_text())
for item in manifest['files']:
    path = root/item['path']
    data = path.read_bytes()
    if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
        raise ValueError('Release file differs: '+item['path'])
print(json.dumps({'status': 'PASS', 'release_files_verified': len(manifest['files'])}))
