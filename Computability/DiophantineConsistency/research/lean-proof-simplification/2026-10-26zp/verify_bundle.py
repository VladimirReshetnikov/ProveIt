#!/usr/bin/env python3
"""Verify the delivered SHA-256 manifest without compiling or modifying files."""
from __future__ import annotations
import hashlib
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent
failures = []
count = 0
for line in (root / 'MANIFEST.sha256').read_text().splitlines():
    expected, relative = line.split('  ', 1)
    target = (root / relative).resolve()
    if not target.is_relative_to(root) or not target.is_file():
        failures.append(relative + ': missing or invalid path')
        continue
    observed = hashlib.sha256(target.read_bytes()).hexdigest()
    if observed != expected:
        failures.append(relative + ': checksum mismatch')
    count += 1
if failures:
    print('\n'.join(failures))
    sys.exit(1)
print(f'Checked {count} files; every SHA-256 digest matches.')
