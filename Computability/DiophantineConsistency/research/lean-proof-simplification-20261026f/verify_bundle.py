#!/usr/bin/env python3
"""Offline byte-integrity check, not a Lean proof checker.

The manifest authenticates consistency with this package, not its publisher.
Use the pinned Git blob hashes in provenance/source_manifest.json to compare
the inspected sources independently with the repository.
"""
import argparse
import hashlib
import json
from pathlib import Path

def check(root, strict=False):
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    seen = set()
    errors = []
    for item in manifest['files']:
        name = item['path']
        path = root / name
        if name in seen or not path.resolve().is_relative_to(root.resolve()):
            errors.append('Invalid or duplicate manifest path: ' + name)
            continue
        seen.add(name)
        if not path.is_file():
            errors.append('Missing file: ' + name)
            continue
        data = path.read_bytes()
        if len(data) != item['bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            errors.append('Changed file: ' + name)
    if strict:
        actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
        errors.extend('Unexpected file: ' + name for name in sorted(actual - seen - {'MANIFEST.json'}))
    return {'status': 'FAIL' if errors else 'PASS_BYTE_INTEGRITY_ONLY',
            'files_checked': len(seen), 'errors': errors,
            'lean_compilation': 'not performed by this tool'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--strict', action='store_true', help='Also reject extra files, including build caches.')
    args = parser.parse_args()
    result = check(Path(__file__).resolve().parent, args.strict)
    print(json.dumps(result, indent=2))
    raise SystemExit(bool(result['errors']))
