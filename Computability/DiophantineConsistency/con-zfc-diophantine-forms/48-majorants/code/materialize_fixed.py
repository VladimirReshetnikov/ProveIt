#!/usr/bin/env python3
"""Materialize and verify the complete fixed leaves of the supplied equations.

Payloads are unsigned little-endian magnitudes, gzip-compressed with mtime=0.
The manifest stores the sign separately. Only Python's standard library is used.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def values():
    spec = json.loads((ROOT / 'data/coefficient_recipes.json').read_text())
    ports = [
        int.from_bytes(gzip.decompress((ROOT / 'data/ports' / (name + '.bin.gz')).read_bytes()), 'little')
        for name in ('beta', 'K', 'MC', 'MF_source')
    ]
    result = {'base_floor': 1 << spec['beta_source_exponent']}
    for name, recipe in spec['recipes'].items():
        total = 0
        for term in recipe:
            value = term['coefficient']
            for port, exponent in zip(ports, term['powers']):
                value *= port ** exponent
            total += value
        result[name] = total
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true', help='verify saved bytes without rewriting')
    args = parser.parse_args()
    dest = ROOT / 'data/fixed'
    computed = values()
    manifest = {
        'format': 'unsigned little-endian magnitude; separate sign; gzip mtime zero',
        'recipe_binding': '../coefficient_recipes.json',
        'values': {},
    }
    for name, value in computed.items():
        raw = abs(value).to_bytes(max(1, (abs(value).bit_length() + 7) // 8), 'little')
        entry = {
            'path': name + '.bin.gz',
            'sign': 0 if value == 0 else 1 if value > 0 else -1,
            'bits': abs(value).bit_length(),
            'bytes': len(raw),
            'raw_sha256': hashlib.sha256(raw).hexdigest(),
        }
        manifest['values'][name] = entry
        if args.check:
            actual = gzip.decompress((dest / entry['path']).read_bytes())
            need(actual == raw, 'fixed payload differs from exact recipe: ' + name)
        else:
            dest.mkdir(parents=True, exist_ok=True)
            (dest / entry['path']).write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
    if args.check:
        need(json.loads((dest / 'MANIFEST.json').read_text()) == manifest, 'fixed manifest differs')
    else:
        (dest / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({
        'status': 'PASS',
        'fixed_leaves': len(computed),
        'raw_bytes': sum(e['bytes'] for e in manifest['values'].values()),
        'mode': 'check' if args.check else 'materialize',
    }))


if __name__ == '__main__':
    main()

