#!/usr/bin/env python3
"""Verify the delivered files against the SHA-256 manifest."""
import hashlib
from pathlib import Path

root = Path(__file__).resolve().parents[1]
count = 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, name = line.split('  ', 1)
    path = (root / name).resolve()
    if not path.is_relative_to(root):
        raise SystemExit('Invalid manifest path: ' + name)
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit('Hash mismatch: ' + name)
    count += 1
print(f'PASS: {count} file hashes match.')
