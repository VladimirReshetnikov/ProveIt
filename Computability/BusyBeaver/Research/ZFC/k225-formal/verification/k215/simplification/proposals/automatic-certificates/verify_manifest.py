#!/usr/bin/env python3
"""Verify delivered file identity. This does not replace formal proof checking."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root/'MANIFEST.sha256.json').read_text())
missing, changed = [], []
for entry in manifest['files']:
    path = root/entry['path']
    if not path.is_file():
        missing.append(entry['path'])
    elif hashlib.sha256(path.read_bytes()).hexdigest() != entry['sha256']:
        changed.append(entry['path'])
print(json.dumps(dict(checked=len(manifest['files']), missing=missing,
                     changed=changed, passed=not missing and not changed), indent=2))
raise SystemExit(bool(missing or changed))
