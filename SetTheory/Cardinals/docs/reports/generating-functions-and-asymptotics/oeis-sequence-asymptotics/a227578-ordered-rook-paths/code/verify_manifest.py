#!/usr/bin/env python3
"""Check every pinned package file against MANIFEST.sha256."""
from pathlib import Path
import hashlib
root = Path(__file__).resolve().parent.parent
lines = (root/'MANIFEST.sha256').read_text().splitlines()
for line in lines:
    expected, name = line.split('  ', 1)
    path = root/name
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit('Hash mismatch: ' + name)
print('Verified', len(lines), 'pinned files')
