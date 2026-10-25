#!/usr/bin/env python3
"""Exercise cache exclusion and authentic-source rejection in a temporary copy."""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIXTURES = ['vendor/__pycache__/fixture.cpython-312.pyc',
            'source/fixture.pyc', 'source/fixture.pyo']

def run():
    python = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    with tempfile.TemporaryDirectory(prefix='round17-cache-controls-') as td:
        root = Path(td) / 'direct'
        shutil.copytree(HERE, root, ignore=shutil.ignore_patterns(
            '__pycache__', '*.pyc', '*.pyo'))
        for name in FIXTURES:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'Inert cache exclusion fixture; never imported.')
        result = subprocess.run(python + [str(root / 'seal.py')],
                                capture_output=True, text=True)
        if result.returncode:
            raise ValueError(result.stderr)
        for name in ('SOURCE_PINS.json', 'MANIFEST.json'):
            files = json.loads((root / name).read_bytes())['files']
            if any('__pycache__' in Path(p).parts or
                   Path(p).suffix in ('.pyc', '.pyo') for p in files):
                raise ValueError('Cache included in ' + name)
        path = root / 'source/source.json'
        path.write_bytes(path.read_bytes() + b'\n')
        result = subprocess.run(python + [str(root / 'seal.py')],
                                capture_output=True, text=True)
        if not result.returncode or ('Existing authentic source pin changed: '
                                     'source/source.json') not in result.stderr:
            raise ValueError('Authentic source change not rejected')
    return {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
            'cache_inventory_exclusion_fixtures': FIXTURES,
            'inventories_checked': ['SOURCE_PINS.json', 'MANIFEST.json'],
            'authentic_source_mutation_rejected': True,
            'runtime': 'Python -B with parent optimization propagated, in a disposable cache-free copy; '
                       'inert fixtures never imported'}

if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))
