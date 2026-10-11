#!/usr/bin/env python3
"""Verify the supplied SHA256SUMS without modifying any package files."""
from __future__ import annotations
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.is_file():
        raise SystemExit('SHA256SUMS is missing.')
    failures = []
    count = 0
    for line in manifest.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        expected, relative = line.split('  ', 1)
        path = (ROOT / relative).resolve()
        if ROOT not in path.parents or not path.is_file():
            failures.append(f'Missing or invalid path: {relative}')
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        count += 1
        if actual != expected:
            failures.append(f'Changed: {relative}')
    if failures:
        raise SystemExit('\n'.join(failures))
    print(f'All {count} listed files match SHA256SUMS.')


if __name__ == '__main__':
    main()
