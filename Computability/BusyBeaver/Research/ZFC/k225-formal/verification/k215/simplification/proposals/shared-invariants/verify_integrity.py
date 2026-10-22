#!/usr/bin/env python3
"""Verify the distributed file manifest; this does not check proof correctness."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'SHA256SUMS.json').read_text())
failed = []
for entry in manifest['files']:
    path = root / entry['path']
    if not path.is_file():
        failed.append((entry['path'], 'missing'))
        continue
    data = path.read_bytes()
    if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
        failed.append((entry['path'], 'size or SHA-256 mismatch'))
if failed:
    for name, reason in failed:
        print(f'{name}: {reason}')
    raise SystemExit(1)
print(f"PASS: {len(manifest['files'])} distributed files match the manifest.")
print('Manifest integrity is separate from the compiler/kernel checks in the receipts.')
