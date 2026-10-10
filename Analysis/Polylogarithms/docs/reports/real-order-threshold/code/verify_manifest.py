#!/usr/bin/env python3
"""Verify all SHA-256 entries in MANIFEST.sha256; this is not a proof checker."""
from __future__ import annotations
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[1]
if __name__=='__main__':
    manifest=ROOT/'MANIFEST.sha256'
    if not manifest.is_file():
        raise SystemExit('MANIFEST.sha256 is missing.')
    count=0
    for line in manifest.read_text().splitlines():
        if not line.strip():
            continue
        expected,name=line.split('  ',1)
        target=(ROOT/name).resolve()
        if ROOT.resolve() not in target.parents:
            raise SystemExit('Unsafe manifest path: '+name)
        if not target.is_file():
            raise SystemExit('Missing file: '+name)
        actual=hashlib.sha256(target.read_bytes()).hexdigest()
        if actual!=expected:
            raise SystemExit('SHA-256 mismatch: '+name)
        count+=1
    print(f'PASS: {count} package files match the supplied manifest.')
