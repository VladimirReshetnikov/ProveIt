#!/usr/bin/env python3
"""Verify every byte hash in the delivered construction manifest."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
for entry in manifest['files']:
    data = (root / entry['path']).read_bytes()
    if len(data) != entry['size'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
        raise SystemExit('Manifest mismatch: ' + entry['path'])
print('Verified', len(manifest['files']), 'file hashes.')
