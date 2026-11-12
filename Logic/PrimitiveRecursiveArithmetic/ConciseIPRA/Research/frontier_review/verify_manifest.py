#!/usr/bin/env python3
"""Verify packaged files against MANIFEST.sha256."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
failures = []
count = 0
for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
    expected, relative = line.split('  ', 1)
    path = ROOT / relative
    observed = hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
    if observed != expected:
        failures.append(relative)
    count += 1
if failures:
    raise SystemExit('Checksum mismatch: ' + ', '.join(failures))
print(f'OK: {count} files match the manifest')
