#!/usr/bin/env python3
"""Verify every frozen package member using portable standard-library SHA-256."""
import hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    path=root/name
    assert path.is_file(), f'Missing: {name}'
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual==digest, f'Hash mismatch: {name}'
    print(f'OK {name}')
print('PASS all package member hashes')
