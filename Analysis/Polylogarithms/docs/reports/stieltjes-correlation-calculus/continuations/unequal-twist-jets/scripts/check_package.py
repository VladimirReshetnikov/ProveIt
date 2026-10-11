#!/usr/bin/env python3
"""Check the delivered SHA-256 receipts. This does not rerun mathematics."""
from __future__ import annotations
import hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def main()->None:
    manifest=ROOT/'SHA256SUMS'
    if not manifest.is_file():raise SystemExit('Missing SHA256SUMS.')
    checked=0
    for line in manifest.read_text().splitlines():
        digest,name=line.split('  ',1)
        target=(ROOT/name).resolve()
        if not target.is_relative_to(ROOT):raise SystemExit(f'Unsafe path in manifest: {name}')
        if not target.is_file():raise SystemExit(f'Missing file: {name}')
        actual=hashlib.sha256(target.read_bytes()).hexdigest()
        if actual!=digest:raise SystemExit(f'Digest mismatch: {name}')
        checked+=1
    print(f'PASS: {checked} file digests match. This is an integrity check, not a proof check.')

if __name__=='__main__':main()
