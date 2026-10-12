#!/usr/bin/env python3
"""Verify SHA256SUMS for the delivered package without modifying any file."""
from __future__ import annotations
import hashlib
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    manifest=ROOT/'SHA256SUMS'
    if not manifest.is_file():
        raise SystemExit('Missing SHA256SUMS; this check does not generate one.')
    count=0
    for line in manifest.read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        expected,name=line.split('  ',1)
        path=(ROOT/name).resolve()
        if not path.is_relative_to(ROOT):
            raise SystemExit(f'Unsafe manifest path: {name}')
        if not path.is_file():
            raise SystemExit(f'Missing file: {name}')
        got=hashlib.sha256(path.read_bytes()).hexdigest()
        if got != expected:
            raise SystemExit(f'Checksum mismatch: {name}')
        count+=1
    print(f'PASS: {count} delivered files match SHA256SUMS.')

if __name__=='__main__':
    main()
