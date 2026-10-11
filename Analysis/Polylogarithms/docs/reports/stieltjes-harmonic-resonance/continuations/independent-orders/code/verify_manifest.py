#!/usr/bin/env python3
"""Verify SHA256SUMS for the delivered package before regenerating artifacts."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parents[1]
failures = []
count = 0
for line in (root / 'SHA256SUMS').read_text().splitlines():
    if not line.strip():
        continue
    expected, name = line.split('  ', 1)
    path = (root / name).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        failures.append(name + ': missing or invalid path')
        continue
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    count += 1
    if actual != expected:
        failures.append(name + ': SHA256 mismatch')
for failure in failures:
    print(failure)
print(f'{count} files checked; {len(failures)} failures.')
sys.exit(bool(failures))
