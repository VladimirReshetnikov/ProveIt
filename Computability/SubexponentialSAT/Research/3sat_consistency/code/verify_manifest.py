#!/usr/bin/env python3
"""Verify the shipped files before rebuilding or regenerating results."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for record in manifest['files']:
        relative = Path(record['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Unsafe manifest path')
        path = ROOT/relative
        raw = path.read_bytes()
        if len(raw) != record['bytes'] or hashlib.sha256(raw).hexdigest() != record['sha256']:
            raise ValueError('File differs: '+str(relative))
    print(json.dumps({'status':'PASS','verified_files':len(manifest['files'])},indent=2))


if __name__ == '__main__':
    main()
