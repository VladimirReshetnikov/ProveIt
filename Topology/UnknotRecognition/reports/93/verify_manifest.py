#!/usr/bin/env python3
"""Verify the release's listed file contents without external dependencies."""

import hashlib
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent
    count = 0
    for line in (root / 'SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts:
            raise SystemExit('Unsafe manifest path')
        path = root / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f'Content mismatch: {name}')
        count += 1
    print(f'All {count} listed file hashes verified.')


if __name__ == '__main__':
    main()
