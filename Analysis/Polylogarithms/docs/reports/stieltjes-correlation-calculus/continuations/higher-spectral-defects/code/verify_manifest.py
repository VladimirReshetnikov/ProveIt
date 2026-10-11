#!/usr/bin/env python3
"""Verify original delivered files against SHA256SUMS (no third-party packages)."""
from pathlib import Path
import hashlib
import sys

def main() -> int:
    root = Path(__file__).resolve().parents[1]
    manifest = root / 'SHA256SUMS'
    if not manifest.is_file():
        print('Missing SHA256SUMS', file=sys.stderr)
        return 2
    count = 0
    failures = []
    for line in manifest.read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        digest, name = line.split('  ', 1)
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            failures.append(f'Missing or unsafe path: {name}')
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != digest:
            failures.append(f'Hash mismatch: {name}')
        count += 1
    if failures:
        print('\n'.join(failures), file=sys.stderr)
        return 1
    print(f'PASS: {count} files match SHA256SUMS.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
