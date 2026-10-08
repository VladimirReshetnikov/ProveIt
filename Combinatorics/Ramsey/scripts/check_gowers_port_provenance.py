#!/usr/bin/env python3
"""Check the quantitative port against a local pinned openai/math checkout.

This checks source provenance and retained notices, not legal compliance or
Lean proofs. It does not download or modify either checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PORT = ROOT / 'lib/openai-math'


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('upstream', type=Path, help='local openai/math repository root')
    args = parser.parse_args()
    manifest = json.loads((PORT / 'quantitative-port-manifest.json').read_text())
    revision = subprocess.check_output(
        ['git', '-C', str(args.upstream), 'rev-parse', 'HEAD'], text=True).strip()
    require(revision == manifest['revision'], 'Upstream checkout is not at the pinned revision')
    upstream = args.upstream / 'lean'
    original_license = subprocess.check_output(
        ['git', '-C', str(args.upstream), 'show', f'{revision}:lean/LICENSE'])
    require((PORT / 'LICENSE').read_bytes() == original_license,
            'The vendored Apache license differs from the pinned upstream license')
    provenance = (PORT / manifest['provenance_notice']).read_text()
    require(manifest['revision'] in provenance and manifest['upstream'] in provenance,
            'The provenance notice does not identify the pinned upstream source')
    modified = 0
    for entry in manifest['modules']:
        path = Path(*entry['module'].split('.')).with_suffix('.lean')
        original = (upstream / path).read_bytes()
        local = (PORT / 'lean' / path).read_bytes()
        require(hashlib.sha256(original).hexdigest() == entry['upstream_sha256'],
                f'Original-source hash mismatch: {path}')
        if local != original:
            modified += 1
            require(b'Modified for ProveIt' in local,
                    f'Missing local modification notice: {path}')
        for line in original.splitlines():
            if b'copyright' in line.lower():
                require(line.strip() in local,
                        f'Missing original copyright notice: {path}')
    for entry in manifest.get('mathlib_backports', []):
        path = Path(*entry['module'].split('.')).with_suffix('.lean')
        require(entry['copyright'] in (PORT / 'lean' / path).read_text(),
                f'Missing recorded Mathlib copyright notice: {path}')
        require((PORT / entry['license_file']).is_file(),
                f'Missing recorded Mathlib license: {entry["license_file"]}')
    print(f'{len(manifest["modules"])} pinned upstream hashes match; '
          f'{modified} adapted files have modification notices.')
    print('Upstream license unchanged; pinned provenance and recorded copyright notices retained.')
    print('Separate Mathlib source hashes are recorded in the manifest, not checked by this command.')


if __name__ == '__main__':
    main()
