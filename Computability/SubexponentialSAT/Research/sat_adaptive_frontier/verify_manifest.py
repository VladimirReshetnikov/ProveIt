#!/usr/bin/env python3
"""Check the delivered SHA-256 manifest without external dependencies."""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        target = (ROOT / name).resolve()
        if not target.is_relative_to(ROOT):
            raise RuntimeError('Unsafe manifest path: ' + name)
        actual = hashlib.sha256(target.read_bytes()).hexdigest()
        if actual != digest:
            raise RuntimeError('SHA-256 mismatch: ' + name)
        count += 1
    print('PASS: ' + str(count) + ' file hashes match.')


if __name__ == '__main__':
    main()
