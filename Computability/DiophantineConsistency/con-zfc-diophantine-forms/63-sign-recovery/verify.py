#!/usr/bin/env python3
"""Reproduce the finite arithmetic checks; no third-party Python packages.

This verifies literal finite data. It neither tests consistency nor replaces
the manuscript's unbounded mathematical proofs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PIN = 'beb0192cb8dc36f78c369c080f2adfbc1887a486'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def release_manifest():
    path = ROOT / 'MANIFEST.sha256'
    require(path.is_file(), 'Missing release manifest; extract the complete archive.')
    count = 0
    for line in path.read_text().splitlines():
        expected, name = line.split('  ', 1)
        file = (ROOT / name).resolve()
        require(file.is_relative_to(ROOT), 'Manifest path escapes package: ' + name)
        require(file.is_file(), 'Missing release file: ' + name)
        require(sha256(file) == expected, 'Release hash differs: ' + name)
        count += 1
    require(count > 80, 'Incomplete release manifest')
    print(f'PASS: {count} release-file hashes', file=sys.stderr)
    return count


def source_provenance():
    main = json.loads((ROOT / 'provenance/SOURCES.json').read_text())
    require(main['commit'] == PIN, 'Main source pin')
    for entry in main['files']:
        raw = (ROOT / entry['local_path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == entry['sha256'],
                'Inherited source hash: ' + entry['local_path'])
        blob = b'blob ' + str(len(raw)).encode() + b'\0' + raw
        require(hashlib.sha1(blob).hexdigest() == entry['git_blob_sha1'],
                'Git blob identity: ' + entry['local_path'])
    nine = json.loads((ROOT / 'nine/SOURCE_PINS.json').read_text())
    require(nine['commit'] == PIN, 'Nine-variable source pin')
    for entry in nine['imported']:
        require(sha256(ROOT / 'nine' / entry['path']) == entry['delivered_sha256'],
                'Nine inherited source hash: ' + entry['path'])
        if entry['mode'] == 'verbatim':
            require(entry['source_sha256'] == entry['delivered_sha256'],
                    'Verbatim source identity: ' + entry['path'])
    out = {'main_inherited_files': len(main['files']),
           'nine_component_imports': len(nine['imported'])}
    print('PASS: pinned inherited source identities', file=sys.stderr)
    return out


def run(label, relative, *arguments, optimized=False, json_output=True):
    env = dict(os.environ)
    env.pop('PYTHONOPTIMIZE', None)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    command = [sys.executable]
    if optimized:
        command.append('-O')
    command.extend([str(ROOT / relative), *(str(a) for a in arguments)])
    result = subprocess.run(command, cwd=ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError(label + ' failed')
    print('PASS: ' + label, file=sys.stderr)
    return json.loads(result.stdout) if json_output else result.stdout.splitlines()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--development', action='store_true',
                        help='authoring only: omit the release-manifest check')
    parser.add_argument('--receipt', type=Path,
                        help='also write the deterministic verification receipt')
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required')
    if not args.development:
        release_manifest()
    provenance = source_provenance()

    with tempfile.TemporaryDirectory(prefix='con-zfc-coefficients-') as temp:
        output = Path(temp) / 'payloads'
        rebuilt = run('rebuild all four main coefficients',
                      'coefficients/build_coefficients.py', '--output', output)
        for name in ('beta', 'K', 'MC', 'MF_source'):
            require((output / (name + '.bin')).read_bytes() ==
                    (ROOT / 'coefficients/payloads' / (name + '.bin')).read_bytes(),
                    'Rebuilt raw coefficient mismatch: ' + name)
        require(rebuilt['raw_bytes'] == 532479, 'Main coefficient byte total')
        print('PASS: rebuilt coefficient bytes match all fixed payloads', file=sys.stderr)

    independent_coefficients = run('independent main-coefficient decoder',
                                   'coefficients/verify_independent.py')
    quartic = run('literal quartic, exact expansion and degree',
                  'quartic/build_verify.py')
    quartic_optimized = run('quartic checks with assertions optimized away',
                            'quartic/build_verify.py', optimized=True)
    require(quartic == quartic_optimized, 'Quartic optimized-mode comparison')
    p14 = run('fourteen-positive formula and exact degree', 'positive14/verify.py')
    p14_optimized = run('fourteen-positive checks under Python -O',
                        'positive14/verify.py', optimized=True)
    require(p14 == p14_optimized, 'P14 optimized-mode comparison')
    nine = run('nine-positive source, majorant, finalizer and degree', 'nine/verify.py')
    independent_nine = run('independent exact majorant and norm identities',
                            'reviews/check_nine_independent.py', json_output=False)

    receipt = {
        'status': 'PASS',
        'source_pin': PIN,
        'dependencies': 'Python >= 3.10; standard library only',
        'provenance': provenance,
        'main_coefficients_rebuilt_and_byte_compared': 4,
        'independent_coefficient_decoder': independent_coefficients,
        'quartic': quartic,
        'positive14': p14,
        'nine': nine,
        'independent_nine_checks': independent_nine,
        'optimized_mode_replays': ['quartic/build_verify.py', 'positive14/verify.py'],
        'semantic_boundary': 'Finite arithmetic and data verification; the unbounded '
                             'existence equivalences are the manuscript proofs composed '
                             'with their named inherited theorems. No new end-to-end '
                             'proof-assistant or object-language ZFC certificate.'
    }
    raw = json.dumps(receipt, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(raw)
    print(raw, end='')


if __name__ == '__main__':
    main()
