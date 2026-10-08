#!/usr/bin/env python3
"""Verify every listed release file without relying on external packages."""
from pathlib import Path,PurePosixPath
import hashlib,sys
ROOT=Path(__file__).resolve().parents[1]

def main():
    manifest=ROOT/'SHA256SUMS'
    if not manifest.is_file():print('Missing SHA256SUMS',file=sys.stderr);return 1
    count=0;failed=[]
    for line in manifest.read_text().splitlines():
        digest,relative=line.split('  ',1);name=PurePosixPath(relative)
        if name.is_absolute() or '..' in name.parts:raise ValueError('unsafe manifest path')
        path=ROOT/relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:failed.append(relative)
        count+=1
    if failed:
        print('FAILED: '+', '.join(failed));return 1
    print(f'Verified {count} release files.');return 0
if __name__=='__main__':raise SystemExit(main())
