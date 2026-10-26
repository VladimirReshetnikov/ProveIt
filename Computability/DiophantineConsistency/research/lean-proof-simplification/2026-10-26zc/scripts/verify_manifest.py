#!/usr/bin/env python3
"""Verify the distributed files against MANIFEST.sha256; never changes files."""
from pathlib import Path
import hashlib
import sys


def main():
    root = Path(__file__).resolve().parent.parent
    manifest = root / 'MANIFEST.sha256'
    errors = []
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = root / relative
        if not path.resolve().is_relative_to(root) or path.is_symlink():
            errors.append(f'Unsafe path: {relative}')
            continue
        if not path.is_file():
            errors.append(f'Missing file: {relative}')
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            errors.append(f'Hash mismatch: {relative}')
        count += 1
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'All {count} manifest entries match SHA-256.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
