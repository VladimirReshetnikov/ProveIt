#!/usr/bin/env python3
"""Verify the declared payload digests. This is not a kernel proof checker."""
from pathlib import Path
import argparse
import hashlib
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.packet.resolve()
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    failures = []
    for relative, item in manifest['files'].items():
        path = (root / relative).resolve()
        if root not in path.parents:
            failures.append(f'Path escapes packet: {relative}')
            continue
        if not path.is_file():
            failures.append(f'Missing: {relative}')
            continue
        data = path.read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            failures.append(f'Changed: {relative}')
    if failures:
        raise SystemExit('\n'.join(failures))
    print(f"PASS: {len(manifest['files'])} declared payload files match their SHA-256 digests.")
    print('Digest integrity is separate from compiler, kernel, and endpoint verification.')


if __name__ == '__main__':
    main()
