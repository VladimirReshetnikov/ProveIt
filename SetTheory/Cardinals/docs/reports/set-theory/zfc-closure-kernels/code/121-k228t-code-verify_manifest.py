#!/usr/bin/env python3
"""Verify the exact bytes listed in the release SHA256SUMS manifest."""
from pathlib import Path
import argparse, hashlib


def verify(package):
    root=package.resolve()
    rows=(root/'SHA256SUMS').read_text().splitlines()
    for row in rows:
        expected,name=row.split('  ',1)
        path=(root/name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise ValueError('Invalid manifest path: '+name)
        if hashlib.sha256(path.read_bytes()).hexdigest()!=expected:
            raise ValueError('SHA-256 mismatch: '+name)
    return len(rows)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--package',type=Path,default=Path(__file__).resolve().parent.parent)
    a=ap.parse_args()
    print('PASS: verified',verify(a.package),'manifested files')
