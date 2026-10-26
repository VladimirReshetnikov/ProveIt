#!/usr/bin/env python3
"""Check all packaged file hashes without modifying the packet."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parents[1]
count=0
for line in (root/'MANIFEST.sha256').read_text().splitlines():
    expected,relative=line.split('  ',1)
    file=root/relative
    if hashlib.sha256(file.read_bytes()).hexdigest()!=expected:
        raise SystemExit('MISMATCH: '+relative)
    count+=1
print(f'PASS: {count} file hashes')
