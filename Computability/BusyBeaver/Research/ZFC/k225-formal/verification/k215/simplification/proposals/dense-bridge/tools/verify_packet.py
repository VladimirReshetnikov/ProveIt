#!/usr/bin/env python3
"""Validate the packet's SHA-256 inventory; this is not a proof-kernel check."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root/'manifest.json').read_text())
failures = []
for row in manifest['files']:
    path = root/row['path']
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
        failures.append(row['path'])
if failures:
    raise SystemExit('Integrity failures: '+', '.join(failures))
print('PASS: '+str(len(manifest['files']))+' files match the SHA-256 inventory.')
print('This verifies byte integrity only; see tools/reproduce_all.py for proof checks.')
