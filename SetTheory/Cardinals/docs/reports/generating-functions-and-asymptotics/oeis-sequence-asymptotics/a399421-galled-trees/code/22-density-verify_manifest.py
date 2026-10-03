#!/usr/bin/env python3
"""Verify shipped files without external checksum utilities."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = root / 'MANIFEST.sha256'
count = 0
for line in manifest.read_text(encoding='utf-8').splitlines():
    if not line.strip():
        continue
    expected, relative = line.split('  ', 1)
    p = root / relative
    if not p.is_file() or not p.resolve().is_relative_to(root):
        raise SystemExit(f'Missing or unsafe manifest entry: {relative}')
    actual = hashlib.sha256(p.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'SHA-256 mismatch: {relative}')
    count += 1
print(f'Verified {count} manifest entries')
