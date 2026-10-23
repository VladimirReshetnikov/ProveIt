#!/usr/bin/env python3
"""Offline finite reconstruction and audits; not an unbounded semantic proof."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PIN = '124c07c0b77a9e20e84676514d8b1ff78536ea3f'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def run(script, cwd=None):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run([sys.executable, str(script)],
                            cwd=cwd or ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError('Failed: ' + str(script))
    return result.stdout


def check_release_manifest():
    path = ROOT / 'ARTIFACT_MANIFEST.json'
    if not path.exists():
        print('Release manifest not yet present; authoring run.', flush=True)
        return
    manifest = json.loads(path.read_text())
    for record in manifest['files']:
        raw = (ROOT / record['path']).read_bytes()
        require(len(raw) == record['bytes'] and sha(raw) == record['sha256'],
                'Release file changed: ' + record['path'])
    print('PASS: release hashes (' + str(len(manifest['files'])) + ' files)', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-release-hashes', action='store_true',
                        help='Allow deliberate local edits; inherited source and coefficient hashes remain mandatory.')
    args = parser.parse_args()
    require(__debug__, 'Run without -O: inherited auditors use assertions.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required.')
    try:
        import numpy  # noqa: F401
    except ImportError as error:
        raise SystemExit('Install NumPy as specified in requirements.txt.') from error
    if not args.skip_release_hashes:
        check_release_manifest()
    pins = json.loads((ROOT / 'provenance/SOURCE_PINS.json').read_text())
    require(pins['baseline_commit'] == PIN, 'Wrong baseline pin')
    for record in pins['records']:
        raw = (ROOT / record['local_path']).read_bytes()
        require(sha(raw) == record['sha256'], 'Source hash: ' + record['local_path'])
    print('PASS: pinned inherited sources (' + str(len(pins['records'])) + ')', flush=True)

    binding = json.loads((ROOT / 'coefficients/ports.json').read_text())
    require(binding['base_commit'] == PIN, 'Wrong coefficient binding pin')
    raw_by_name = {}
    for record in binding['ports']:
        packed = (ROOT / 'coefficients' / record['file']).read_bytes()
        raw = gzip.decompress(packed)
        require(sha(packed) == record['gzip_sha256'], 'Compressed coefficient hash')
        require(sha(raw) == record['sha256'] and len(raw) == record['bytes'],
                'Raw coefficient binding')
        require(int.from_bytes(raw, 'little').bit_length() == record['bit_length'],
                'Coefficient bit length')
        packed_copy = (ROOT / 'packing/coefficients/payloads' / record['file']).read_bytes()
        require(packed == packed_copy, 'Packing tuple differs from main tuple')
        raw_by_name[record['source_name']] = raw
    require(len(raw_by_name) == 4, 'Four distinct complete coefficient ports required')
    with tempfile.TemporaryDirectory(prefix='conzfc-native-rebuild-') as td:
        temp = Path(td) / 'native'
        shutil.copytree(ROOT / 'coefficients/upstream', temp)
        run(temp / 'build_coefficients.py', temp)
        for name, raw in raw_by_name.items():
            require((temp / 'payloads' / (name + '.bin')).read_bytes() == raw,
                    'Finite coefficient recipe differs: ' + name)
    print('PASS: finite native recipe and all four active coefficient ports', flush=True)

    stages = [
        ('support packing, both parents, exact degrees', 'packing/verify.py'),
        ('eleven-variable literal circuit generation', 'eleven/build.py'),
        ('eleven-variable norm and exact polynomial degree', 'eleven/check.py'),
        ('fourteen-variable literal circuit generation', 'fourteen/build_fourteen.py'),
        ('fourteen-variable exact symbolic degree and liveness', 'fourteen/check_fourteen.py'),
        ('independent formal-radical multiplication', 'review/audit_midpoint_independent.py'),
    ]
    receipts = []
    for name, filename in stages:
        run(ROOT / filename)
        receipts.append({'check': name, 'script': filename, 'status': 'PASS'})
        print('PASS: ' + name, flush=True)
    metrics = json.loads((ROOT / 'eleven/generated/METRICS.json').read_text())
    expected = {
        'eleven_midpoint_product': (954, 115),
        'eleven_midpoint_system': (952, 111),
        'eleven_midpoint_shifted_system': (952, 110),
        'eleven_full_product': (958, 116),
        'eleven_full_system': (956, 112),
        'eleven_full_shifted_system': (956, 111),
    }
    for row in metrics:
        require((row['exact_degree'], row['ledger']['operations']) == expected[row['name']],
                'Eleven-variable summary mismatch')
    fourteen = json.loads((ROOT / 'fourteen/fourteen_audit.json').read_text())
    require((fourteen['witnesses'], fourteen['exact_degree'], fourteen['operations'])
            == (14, 56, 79), 'Fourteen-variable summary mismatch')
    result = {
        'status': 'PASS', 'baseline_commit': PIN,
        'pinned_source_files_checked': len(pins['records']),
        'complete_coefficient_tuple_regenerated': True,
        'coefficient_payload_bytes': sum(map(len, raw_by_name.values())),
        'checks': receipts,
        'principal_results': [
            {'domain': 'strictly positive integers', 'variables': 9,
             'degree': 30947584, 'operations': 651},
            {'domain': 'nonnegative integers', 'variables': 9,
             'degree': 30947584, 'operations': 654},
            {'domain': 'unrestricted integers', 'variables': 10,
             'degree': 56593864, 'operations': 653},
            {'domain': 'strictly positive integers', 'variables': 11,
             'degree': 954, 'operations': 115},
            {'domain': 'strictly positive integers', 'variables': 14,
             'degree': 56, 'operations': 79},
        ],
        'scope': 'Finite reconstruction and arithmetic certificates. Universal new reductions are proved in report.tex; semantic compiler and K215 calibration are inherited mathematical dependencies.',
        'new_end_to_end_lean_certificate': False,
        'global_minimality_claim': False,
    }
    (ROOT / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All finite checks passed. Receipt: VERIFICATION.json', flush=True)


if __name__ == '__main__':
    main()
