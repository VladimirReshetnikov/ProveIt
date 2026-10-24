#!/usr/bin/env python3
"""Offline, non-mutating replay of the delivered finite certificates.

All work that writes files takes place in a temporary copy. This script
does not certify the unbounded semantic theorems or search for a zero.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, label):
    if not condition:
        raise RuntimeError(label)


def authenticate_sources():
    ledger = json.loads((ROOT/'SOURCE_PROVENANCE.json').read_text())
    for entry in ledger['entries']:
        path = Path(entry['file'])
        require(not path.is_absolute() and '..' not in path.parts, 'relative source path')
        raw = (ROOT/path).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == entry['sha256'], 'source hash '+str(path))
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob == entry['git_blob_sha1'], 'source Git identity '+str(path))
    return len(ledger['entries'])


def run(root, script):
    print('Checking '+script, file=sys.stderr, flush=True)
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    # Keep all explicit checks active, including when the entry point is
    # run with -O. None of the release checks depends on Python assertions.
    if not __debug__:
        env['PYTHONOPTIMIZE'] = '1'
    result = subprocess.run([sys.executable, str(root/script)], cwd=root,
                            env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(script+' failed:\n'+result.stdout[-8000:]+'\n'+result.stderr[-8000:])


def snapshots(directory, pattern):
    return {p.name: p.read_bytes() for p in sorted(directory.glob(pattern))}


def read(root, name):
    return json.loads((root/name).read_text())


def main():
    sources = authenticate_sources()
    with tempfile.TemporaryDirectory(prefix='con-zfc-release-') as directory:
        temp = Path(directory)/'release'
        shutil.copytree(ROOT, temp, ignore=shutil.ignore_patterns(
            '__pycache__', '*.pyc', '*.aux', '*.log', '*.out', '*.toc',
            '*.fdb_latexmk', '*.fls'))

        run(temp, 'coefficients/verify.py')
        old_integer = snapshots(temp/'integer', '*.json')
        run(temp, 'integer/build.py')
        require(old_integer == snapshots(temp/'integer', '*.json'), 'byte-identical integer rebuild')
        run(temp, 'integer/audit.py')

        for parent in (temp/'transport/parents').glob('*.json'):
            require(parent.read_bytes() == (temp/'integer'/parent.name).read_bytes(),
                    'transport parent is exact audited integer packet '+parent.name)
        old_transport = snapshots(temp/'transport', 'degree*.json')
        run(temp, 'transport/build_transport.py')
        require(old_transport == snapshots(temp/'transport', 'degree*.json'), 'byte-identical transport rebuild')
        run(temp, 'transport/check_transport.py')

        run(temp, 'positive/verify.py')
        nine_literal = (temp/'nine_full_radical/laurent9_positive.json').read_bytes()
        run(temp, 'nine_full_radical/build.py')
        require(nine_literal == (temp/'nine_full_radical/laurent9_positive.json').read_bytes(),
                'byte-identical nine-variable circuit rebuild')
        run(temp, 'nine_full_radical/verify.py')

        integer = read(temp, 'certificates/INDEPENDENT_INTEGER_AUDIT.json')
        transport = read(temp, 'transport/certificates/INDEPENDENT_TRANSPORT_AUDIT.json')
        coefficients = read(temp, 'coefficients/VERIFICATION.json')
        positive = read(temp, 'positive/VERIFICATION.json')
        nine = read(temp, 'nine_full_radical/VERIFICATION.json')
        for title, result in [('integer', integer), ('transport', transport),
                              ('coefficients', coefficients), ('positive', positive), ('nine', nine)]:
            require(result['status'] == 'PASS', title+' audit receipt')
        result = {
            'status': 'PASS',
            'source_snapshot': 'cf4a5218a5a4e4358d3f5314151b6b05d4aa384e',
            'authenticated_main_source_files': sources,
            'integer_expanded_packets_rebuilt_byte_identically': len(old_integer),
            'integer_independent_exact_checks': integer['checks'],
            'transport_packets_rebuilt_byte_identically': len(old_transport),
            'transport_independent_exact_checks': transport['checks'],
            'integer_fixed_numerals_reconstructed': len(coefficients['fixed_numerals']),
            'integer_fixed_numerals_raw_bytes': coefficients['raw_bytes'],
            'positive': positive,
            'nine_positive': {
                'degree': nine['exact_degree'], 'operations': nine['total_operations'],
                'literal_rebuild': 'byte identical',
                'cone_certificate_terms': nine['cone_terms'],
                'coefficient_reconstruction': nine['coefficient_reconstruction']},
            'transport_equations': transport['metrics'],
            'scope': 'Exact finite coefficient, literal-polynomial, identity, domain-dimension and degree checks. Inherited unbounded native/Pell/refutation theorems remain explicit mathematical dependencies; no new end-to-end proof-assistant certificate.'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
