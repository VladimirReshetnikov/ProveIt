#!/usr/bin/env python3
"""Refresh local release inventories, never treating Python caches as source."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def cache_path(path):
    return '__pycache__' in path.parts or path.suffix in ('.pyc', '.pyo')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write(path, data):
    path.write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')

def files(root):
    return [p for p in sorted(root.rglob('*'))
            if p.is_file() and not cache_path(p.relative_to(root))]

def main():
    old = json.loads((HERE / 'SOURCE_PINS.json').read_bytes())['files']
    for name, expected in old.items():
        if not cache_path(Path(name)) and digest(HERE / name) != expected:
            raise ValueError('Existing authentic source pin changed: ' + name)
    pins = {str(p.relative_to(HERE)): digest(p)
            for directory in ('source', 'vendor')
            for p in files(HERE / directory)}
    write(HERE / 'SOURCE_PINS.json', {'files': pins})
    review = json.loads((HERE / 'CODE_REVIEW.json').read_bytes())
    review['reviewed_runtime_files']['seal.py'] = digest(HERE / 'seal.py')
    review['reviewed_runtime_files'] = {
        name: digest(HERE / name) for name in review['reviewed_runtime_files']}
    write(HERE / 'CODE_REVIEW.json', review)
    inventory = {str(p.relative_to(HERE)): {'bytes': p.stat().st_size,
                                           'sha256': digest(p)}
                 for p in files(HERE) if p != HERE / 'MANIFEST.json'}
    write(HERE / 'MANIFEST.json', {
        'schema': 'round17_direct_release_inventory_v1', 'files': inventory})
    print(json.dumps({'manifest_sha256': digest(HERE / 'MANIFEST.json'),
                      'files': len(inventory),
                      'bytes': sum(x['bytes'] for x in inventory.values())}))

if __name__ == '__main__':
    main()
