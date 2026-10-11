#!/usr/bin/env python3
"""Verify the supplied snapshot. Rebuilding output files legitimately changes hashes."""
import hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS'
if not manifest.exists(): raise SystemExit('No SHA256SUMS exists in this directory.')
count=0; errors=[]
for line in manifest.read_text().splitlines():
    digest,name=line.split('  ',1)
    p=root/name
    if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest: errors.append(name)
    count+=1
if errors: raise SystemExit('Mismatch or missing files: '+', '.join(errors))
print(f'PASS: {count} delivered files match SHA256SUMS.')
