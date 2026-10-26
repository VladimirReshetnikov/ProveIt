#!/usr/bin/env python3
"""Verify the extracted, unmodified delivery against its integrity manifest."""
from pathlib import Path
import hashlib
import sys
packet = Path(__file__).resolve().parent.parent
failures = []
count = 0
for line in (packet / 'SHA256SUMS').read_text().splitlines():
    expected, name = line.split('  ', 1)
    target = packet / name
    if not target.is_file():
        failures.append(f'Missing: {name}')
    elif hashlib.sha256(target.read_bytes()).hexdigest() != expected:
        failures.append(f'Changed: {name}')
    count += 1
if failures:
    print('\n'.join(failures))
    sys.exit(1)
print(f'All {count} file hashes match.')
