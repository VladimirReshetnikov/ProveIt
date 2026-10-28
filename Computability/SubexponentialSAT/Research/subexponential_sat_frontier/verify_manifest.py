#!/usr/bin/env python3
"""Verify every sealed payload entry; extra replay/build files are ignored."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for name, expected in manifest['sha256'].items():
    path=ROOT/name
    if not path.is_file():
        raise SystemExit('Missing file: '+name)
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual!=expected:
        raise SystemExit('Hash mismatch: '+name)
print('Verified',len(manifest['sha256']),'payload files.')
