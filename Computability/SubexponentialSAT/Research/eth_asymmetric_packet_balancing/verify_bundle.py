#!/usr/bin/env python3
"""Verify the packaged bytes listed in SHA256SUMS before regenerating outputs."""
from pathlib import Path
import hashlib


def main():
    root = Path(__file__).resolve().parent
    manifest = root / 'SHA256SUMS'
    failures = []
    seen = set()
    for number, line in enumerate(manifest.read_text(encoding='utf-8').splitlines(), 1):
        if not line:
            continue
        digest, separator, relative = line.partition('  ')
        if not separator or len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
            raise SystemExit(f'Invalid checksum record on line {number}')
        candidate = (root / relative).resolve()
        if relative in seen or not candidate.is_relative_to(root) or not candidate.is_file():
            failures.append(relative + ': duplicate, unsafe, or missing path')
            continue
        seen.add(relative)
        actual = hashlib.sha256(candidate.read_bytes()).hexdigest()
        if actual != digest:
            failures.append(relative + ': checksum differs')
    if failures:
        raise SystemExit('\n'.join(failures))
    print(f'PASS: {len(seen)} packaged file checksums match.')
    print('Internal consistency only; this is not a digital signature.')


if __name__ == '__main__':
    main()
