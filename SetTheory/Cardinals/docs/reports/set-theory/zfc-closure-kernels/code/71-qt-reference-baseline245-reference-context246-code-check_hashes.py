#!/usr/bin/env python3
"""Verify release bytes before running checks that refresh result files."""
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    count = 0
    failures = []
    for line in (ROOT / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        if not path.is_file() or sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name)
        count += 1
    if failures:
        raise SystemExit('Release integrity failed: ' + ', '.join(failures))
    print(f'RELEASE INTEGRITY PASS: {count} file hashes match')


if __name__ == '__main__':
    main()
