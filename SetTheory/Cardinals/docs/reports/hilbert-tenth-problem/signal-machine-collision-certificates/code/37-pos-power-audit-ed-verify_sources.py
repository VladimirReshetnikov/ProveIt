#!/usr/bin/env python3
"""Verify candidate manifest coverage, retained source hashes and origins."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate')
    parser.add_argument('--output', default='source_verification.json')
    args = parser.parse_args()
    root = Path(args.candidate)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    seen = set()
    for row in manifest['files']:
        path = root / row['file']
        data = path.read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise AssertionError(str(path))
        seen.add(row['file'])
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    if seen != actual - {'MANIFEST.json'}:
        raise AssertionError('Incomplete manifest coverage')
    pins = json.loads((root / 'SOURCE_PINS.json').read_text())
    for row in pins['retained_sources']:
        data = (root / row['file']).read_bytes()
        original = Path(row['origin']).read_bytes()
        if data != original or len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise AssertionError(row['file'])
    row = pins['additional_source_read_inertly']
    if hashlib.sha256(Path(row['origin']).read_bytes()).hexdigest() != row['sha256']:
        raise AssertionError(row['origin'])
    result = {'candidate_manifest_entries_verified': len(seen),
              'candidate_manifest_complete': True,
              'retained_source_pins_and_origins_verified': len(pins['retained_sources']),
              'additional_inert_source_hash_verified': True}
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
