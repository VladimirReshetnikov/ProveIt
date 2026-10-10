#!/usr/bin/env python3
"""Check packaged bytes against MANIFEST.sha256 (not a mathematical proof)."""
from pathlib import Path
import hashlib

ROOT=Path(__file__).resolve().parents[1]

def main():
    count=0
    for row in (ROOT/'MANIFEST.sha256').read_text().splitlines():
        expected,relative=row.split('  ',1)
        path=(ROOT/relative).resolve()
        if ROOT not in path.parents or not path.is_file():
            raise SystemExit(f'Missing or unsafe manifest path: {relative}')
        actual=hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f'Hash mismatch: {relative}')
        count += 1
    print(f'PASS: {count} file hashes match the manifest.')

if __name__=='__main__':
    main()
