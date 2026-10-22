#!/usr/bin/env python3
"""Verify every file listed in the delivered SHA-256 manifest."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parent.parent
count = 0
for line in (root/'MANIFEST.sha256').read_text().splitlines():
    digest, relative = line.split('  ', 1)
    path = root / relative
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit(f'Hash mismatch: {relative}')
    count += 1
print(f'PASS: {count} delivered files match their SHA-256 hashes.')
