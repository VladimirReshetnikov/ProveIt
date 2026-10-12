#!/usr/bin/env python3
"""Verify every file hash in SHA256SUMS. Rebuilding outputs changes their hashes."""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parent.parent
if __name__ == '__main__':
    count = 0
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest, relative = line.split('  ', 1)
        path = ROOT / relative
        assert path.is_file(), f'Missing file: {relative}'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, relative
        count += 1
    print(f'PASS: {count} SHA-256 file hashes')
