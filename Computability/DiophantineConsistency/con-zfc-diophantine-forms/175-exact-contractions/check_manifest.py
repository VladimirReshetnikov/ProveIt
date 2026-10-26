#!/usr/bin/env python3
"""Check the bytes of every file sealed in MANIFEST_SHA256.json."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    manifest = json.loads((ROOT / 'MANIFEST_SHA256.json').read_text())
    files = manifest['files']
    for name, wanted in files.items():
        path = (ROOT / name).resolve()
        if ROOT not in path.parents or not path.is_file():
            raise ValueError('Missing or invalid manifest path: ' + name)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != wanted:
            raise ValueError('SHA-256 mismatch: ' + name)
    print(json.dumps({'status': 'pass', 'sealed_files': len(files)}))


if __name__ == '__main__':
    main()
