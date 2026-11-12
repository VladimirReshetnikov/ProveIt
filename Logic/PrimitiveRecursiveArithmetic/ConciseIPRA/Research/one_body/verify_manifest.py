#!/usr/bin/env python3
"""Verify the SHA-256 manifest of this research package."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parent
failed = []
count = 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, relative = line.split('  ', 1)
    path = root / relative
    actual = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    count += 1
    if actual != expected:
        failed.append(relative)
if failed:
    print('FAIL:', ', '.join(failed))
    sys.exit(1)
print(f'PASS: {count} file hashes match.')
