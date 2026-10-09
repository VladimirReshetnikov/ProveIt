#!/usr/bin/env python3
"""Verify the delivered manifest; this checks file integrity, not mathematics."""
from pathlib import Path
import hashlib
import json
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    try:
        manifest = json.loads((root / 'package_manifest.json').read_text(encoding='utf-8'))
        failures = []
        for item in manifest['files']:
            relative = Path(item['path'])
            if relative.is_absolute() or '..' in relative.parts:
                failures.append(f"unsafe manifest path: {relative}")
                continue
            path = root / relative
            if not path.is_file():
                failures.append(f"missing: {relative}")
                continue
            data = path.read_bytes()
            if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
                failures.append(f"changed: {relative}")
        for message in failures:
            print(message, file=sys.stderr)
        print(json.dumps({'manifest_files': len(manifest['files']),
                          'integrity_verified': not failures,
                          'scope': 'Integrity of listed delivered files only; not a proof or source-geometry check.'}))
        return 1 if failures else 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'Manifest verification failed: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
