#!/usr/bin/env python3
"""Check the complete package against SHA256SUMS.txt; no dependencies."""

from pathlib import Path
import hashlib


def main():
    root = Path(__file__).resolve().parent
    checked = 0
    for line in (root / 'SHA256SUMS.txt').read_text().splitlines():
        digest, name = line.split('  ', 1)
        file = root / name
        if not file.is_file():
            raise SystemExit(f'Missing file: {name}')
        if hashlib.sha256(file.read_bytes()).hexdigest() != digest:
            raise SystemExit(f'Checksum mismatch: {name}')
        checked += 1
    print(f'All {checked} package file checksums match.')


if __name__ == '__main__':
    main()
