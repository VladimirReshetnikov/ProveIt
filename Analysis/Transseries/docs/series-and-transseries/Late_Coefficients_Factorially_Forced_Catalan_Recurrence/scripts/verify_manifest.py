#!/usr/bin/env python3
"""Verify package bytes without external commands or dependencies."""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parents[1]
count = 0
for line in (root / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
    if not line.strip():
        continue
    digest, name = line.split('  ', 1)
    path = root / name
    if not path.is_file():
        raise SystemExit(f'Missing package file: {name}')
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f'SHA-256 mismatch: {name}')
    count += 1
print(f'All {count} manifest entries verified')
