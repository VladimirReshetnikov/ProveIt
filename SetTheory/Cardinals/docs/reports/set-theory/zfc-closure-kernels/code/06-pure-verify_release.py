#!/usr/bin/env python3
"""Check SHA256SUMS for the delivered release; rebuilding may change outputs."""
from pathlib import Path
import hashlib
import sys
root = Path(__file__).resolve().parent
bad = []
for line in (root / 'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ', 1)
    p = (root / name).resolve()
    if root not in p.parents or not p.is_file():
        bad.append(name)
        continue
    if hashlib.sha256(p.read_bytes()).hexdigest() != digest:
        bad.append(name)
if bad:
    print('Missing or changed files:', *bad, sep='\n')
    sys.exit(1)
print('All listed release files match SHA256SUMS.')
