#!/usr/bin/env python3
"""Replay locally authored integer circuit builders and checkers, without downloads."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
FORMS = [
    ('build_integer26_unscaled.py', 'verify_integer26_unscaled.py', 'INTEGER26_UNSCALED_CHECKS.json'),
    ('build_integer26.py', 'verify_integer26.py', 'INTEGER26_CHECKS.json'),
    ('build_integer27.py', 'verify_integer27.py', 'INTEGER27_CHECKS.json'),
    ('build_integer28_amalgam.py', 'verify_integer28_amalgam.py', 'INTEGER28_AMALGAM_CHECKS.json'),
    ('build_integer28.py', 'verify_integer28.py', 'INTEGER28_CHECKS.json'),
]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--all-backends', action='store_true',
                        help='Also require and verify the separately packaged fallback coefficient binaries.')
    args = parser.parse_args()
    bindings = json.loads((HERE / 'COEFFICIENT_BINDINGS.json').read_text())
    sources = json.loads((HERE / 'SOURCE_MANIFEST.json').read_text())
    verified_sources = []
    for item in sources['sources']:
        path = HERE / item['path']
        assert digest(path) == item['local_sha256'], item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        verified_sources.append(item['path'])
    results = []
    for builder, checker, receipt in FORMS:
        subprocess.run([sys.executable, str(HERE / builder)], cwd=HERE, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        subprocess.run([sys.executable, str(HERE / checker)], cwd=HERE, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        result = json.loads((HERE / receipt).read_text())
        assert result['status'] == 'PASS', receipt
        results.append({
            'build': builder, 'check': checker, 'status': result['status'],
            'degree': result['exact_degree'],
            'counts': {k: result[k] for k in ('operations', 'multiplications', 'additions_subtractions')},
            'circuit_sha256': result['circuit_sha256'],
        })
    for item in bindings['arithmetic_skeletons']:
        assert digest(HERE / item['file']) == item['sha256'], item['file']
    verified_coefficients = []
    backend_names = list(bindings['backends']) if args.all_backends else [bindings['primary_backend']]
    for name in backend_names:
        backend = bindings['backends'][name]
        for item in backend.get('coefficients', {}).values():
            path = HERE / item['path']
            assert item['encoding'] == 'unsigned little-endian, minimal bytes, no header'
            assert digest(path) == item['sha256'], item['path']
            assert int.from_bytes(path.read_bytes(), 'little').bit_length() == item['bit_length']
            verified_coefficients.append(item['path'])
    assert len(verified_coefficients) == (8 if args.all_backends else 4)
    receipt = {
        'status': 'PASS', 'results': results,
        'all_source_hashes_verified': True,
        'verified_source_files': verified_sources,
        'all_arithmetic_binding_hashes_verified': True,
        'selected_backend_coefficient_hashes_verified': True,
        'verified_backends': backend_names,
        'verified_coefficient_files': verified_coefficients,
        'primary_backend': bindings['primary_backend'],
        'scope': 'Finite circuit, polynomial-degree and hash diagnostics supplement the proof notes; no proof-assistant certificate or enormous consistency witness is claimed.',
    }
    (HERE / 'FULL_INTEGER_REPLAY.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
