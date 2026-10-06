#!/usr/bin/env python3
"""Compare complete deterministic JSON receipt directories."""
import argparse
import json
from pathlib import Path


def compare(left, right):
    left, right = Path(left), Path(right)
    if not left.is_dir() or not right.is_dir():
        raise ValueError('both inputs must be receipt directories')
    a = {p.name for p in left.glob('*.json')}
    b = {p.name for p in right.glob('*.json')}
    if not a or a != b:
        raise ArithmeticError('receipt file sets differ or are empty')
    if 'manifest.json' not in a or 'failure.json' in a:
        raise ArithmeticError('missing success manifest or failed run')
    for name in sorted(a):
        l = json.loads((left/name).read_text(encoding='utf-8'))
        r = json.loads((right/name).read_text(encoding='utf-8'))
        if l != r:
            raise ArithmeticError('semantic receipt mismatch: '+name)
        if name == 'manifest.json':
            if l.get('status') != 'PASS':
                raise ArithmeticError('manifest does not report success')
            if set(l.get('receipts', [])) | {'manifest.json'} != a:
                raise ArithmeticError('manifest receipt list does not match the directory')
    return sorted(a)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('left', type=Path)
    parser.add_argument('right', type=Path)
    args = parser.parse_args()
    files = compare(args.left, args.right)
    print('PASS: identical semantic JSON in '+', '.join(files))
