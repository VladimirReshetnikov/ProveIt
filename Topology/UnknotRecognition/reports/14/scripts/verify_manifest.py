#!/usr/bin/env python3
"""Verify every file recorded in MANIFEST.json; extra build outputs are permitted."""
import hashlib
import json
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    failures = []
    for entry in manifest['files']:
        name = PurePosixPath(entry['path'])
        if name.is_absolute() or '..' in name.parts:
            raise ValueError(f'Unsafe manifest path: {name}')
        path = ROOT.joinpath(*name.parts)
        if not path.is_file():
            failures.append(f'missing: {name}')
            continue
        content = path.read_bytes()
        if len(content) != entry['bytes'] or hashlib.sha256(content).hexdigest() != entry['sha256']:
            failures.append(f'changed: {name}')
    if failures:
        raise ValueError('\n'.join(failures))
    print(f"Verified {len(manifest['files'])} files against MANIFEST.json.")


if __name__ == '__main__':
    main()
