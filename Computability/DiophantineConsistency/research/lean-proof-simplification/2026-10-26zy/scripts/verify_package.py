#!/usr/bin/env python3
"""Read-only SHA256SUMS verification of delivered files."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
count = 0
for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    path = (ROOT / name).resolve()
    if ROOT not in path.parents or not path.is_file():
        raise SystemExit(f'Invalid or missing file: {name}')
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f'Hash mismatch: {name}')
    count += 1
print(f'All {count} recorded file hashes match.')
