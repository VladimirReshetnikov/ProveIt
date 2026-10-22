#!/usr/bin/env python3
"""Verify delivered bytes; this is not a mathematical proof checker."""
from pathlib import Path
import hashlib
import json
import sys


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    failures = []
    for item in manifest['files']:
        relative = Path(item['path'])
        if relative.is_absolute() or '..' in relative.parts:
            failures.append('unsafe manifest path: ' + item['path'])
            continue
        path = root / relative
        if not path.is_file():
            failures.append('missing: ' + item['path'])
            continue
        data = path.read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            failures.append('changed: ' + item['path'])
    if failures:
        print('\n'.join(failures), file=sys.stderr)
        return 1
    print(f"PASS: {len(manifest['files'])} delivered files match their recorded bytes.")
    print('Integrity only; replay the proof drivers for focused compiler verification.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
