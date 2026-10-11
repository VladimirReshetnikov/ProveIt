#!/usr/bin/env python3
"""Check SHA-256 hashes of delivered files before any replay/rebuild."""
from pathlib import Path
import hashlib, sys
ROOT=Path(__file__).resolve().parents[1]
def main():
    manifest=ROOT/'SHA256SUMS.txt'
    if not manifest.is_file(): raise SystemExit('SHA256SUMS.txt is missing.')
    count=0;failures=[]
    for line in manifest.read_text().splitlines():
        if not line.strip(): continue
        expected,name=line.split('  ',1)
        p=ROOT/name
        if not p.is_file(): failures.append(f'missing: {name}');continue
        actual=hashlib.sha256(p.read_bytes()).hexdigest()
        if actual!=expected: failures.append(f'changed: {name}')
        count+=1
    if failures:
        print('\n'.join(failures));raise SystemExit(1)
    print(f'PASS: {count} delivered file hashes match. No mathematical proof or new-PDF review is inferred.')
if __name__=='__main__': main()
