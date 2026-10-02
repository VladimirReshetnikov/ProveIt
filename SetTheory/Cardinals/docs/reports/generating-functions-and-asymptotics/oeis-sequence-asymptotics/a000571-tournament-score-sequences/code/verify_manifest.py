#!/usr/bin/env python3
"""Verify each listed package file, without following paths outside the bundle."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parent.parent
manifest=ROOT/'SHA256SUMS'
count=0
for line in manifest.read_text().splitlines():
    if not line.strip():
        continue
    digest, name=line.split('  ',1)
    relative=Path(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError(f'Unsafe manifest path: {name}')
    path=ROOT/relative
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(ROOT):
        raise ValueError(f'Invalid manifest target: {name}')
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        raise ValueError(f'SHA-256 mismatch: {name}')
    count+=1
print(f'PASS: {count} packaged file hashes')
