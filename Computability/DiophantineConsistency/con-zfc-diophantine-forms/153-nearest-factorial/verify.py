#!/usr/bin/env python3
"""Run the release's offline exact checks without modifying its artifacts.

This verifies finite algebra and source bindings. It does not decide the
existence of a zero or replace the ordinary mathematical proofs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def check_manifest():
    path = ROOT / 'MANIFEST_SHA256.json'
    require(path.is_file(), 'Release manifest is missing')
    manifest = json.loads(path.read_text())
    for name, entry in manifest['files'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Invalid manifest path: ' + name)
        data = (ROOT / relative).read_bytes()
        require(len(data) == entry['bytes'], 'Changed file size: ' + name)
        require(hashlib.sha256(data).hexdigest() == entry['sha256'],
                'Changed file content: ' + name)
    return {'files': len(manifest['files']), 'status': 'pass'}


def run(relative, *arguments):
    flags = ['-B'] + (['-O'] if sys.flags.optimize else [])
    command = [sys.executable, *flags, str(ROOT / relative), *arguments]
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run(command, cwd=ROOT, env=env,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(relative + ' failed:\n' + result.stdout + result.stderr)
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(relative + ' did not return its expected JSON receipt:\n'
                           + result.stdout + result.stderr) from error


def check_results():
    inventory = json.loads((ROOT/'RESULTS.json').read_text())
    require(len(inventory['results']) == 7, 'Unexpected result inventory')
    ids = []
    for result in inventory['results']:
        ids.append(result['id'])
        raw = (ROOT/result['equation']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == result['equation_sha256'],
                'Equation inventory binding: ' + result['id'])
        equation = json.loads(raw)
        require((ROOT/result['proof']).is_file(), 'Missing identified proof')
        if result['family'] == 'direct_C222':
            metrics = json.loads((ROOT/result['metrics']).read_text())
            for key, measured in [('variables','variables'), ('exact_degree','degree'),
                                  ('quadratic_residuals','rows'),
                                  ('collected_monomials','monomials'),
                                  ('coefficient_height','height')]:
                require(result[key] == metrics[measured], 'Direct result metric: ' + key)
            expanded = (ROOT/result['expanded_polynomial']).read_bytes()
            require(hashlib.sha256(expanded).hexdigest() == result['expanded_sha256'],
                    'Expanded polynomial inventory binding')
        elif result['family'] == 'signed_native_scalar':
            for key, measured in [('variables','variable_count'), ('exact_degree','exact_degree'),
                                  ('binary_operations','operations'),
                                  ('operation_counts','operation_counts')]:
                require(result[key] == equation[measured], 'Signed result metric: ' + key)
        elif result['family'] == 'positive_native_compact':
            require(result['variables'] == len(equation['witnesses']), 'Compact variable count')
            require(result['exact_degree'] == equation['exact_degree'] == 382, 'Compact degree')
            require(result['binary_operations'] == equation['operations'] == 79, 'Compact cost')
        else:
            raise ValueError('Unknown equation family')
        domain = ('strictly positive integers' if result['family'] == 'positive_native_compact'
                  else 'unrestricted integers')
        require(result['domain'] == domain, 'Incorrect result domain')
    require(len(set(ids)) == 7, 'Duplicate result')
    return {'status':'pass', 'equations':ids}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true',
                        help='Also reconstruct the polynomial artifacts and compare exact bytes')
    parser.add_argument('--receipt', type=Path,
                        help='Optionally write this run receipt; otherwise read-only')
    args = parser.parse_args()
    receipt = {'status': 'pass', 'manifest': check_manifest(),
               'python_optimization': sys.flags.optimize,
               'rebuild_requested': args.rebuild}
    receipt['result_inventory'] = check_results()
    receipt['direct'] = run('direct/verify.py', *(['--rebuild'] if args.rebuild else []))
    receipt['direct_independent_source_audit'] = run('review/audit_direct_source.py')
    receipt['signed'] = run('signed/check.py')
    receipt['signed_independent_audit'] = run('review/audit_signed.py')
    receipt['compact'] = run('compact/verify.py')
    receipt['report_inputs'] = run('code/report_inputs.py', '--check')
    if args.rebuild:
        receipt['signed_reconstruction'] = run('signed/build.py', '--check')
        receipt['compact_reconstruction'] = run('compact/build_partial79.py', '--check')
    receipt['scope'] = (
        'Exact finite identities, source bytes, coefficient reconstruction, degrees, '
        'metrics, corruption controls and report transcription. The unbounded '
        'arithmetic and internal-ZFC calibration are ordinary mathematical proofs; '
        'this is not an end-to-end proof-assistant certificate or a consistency decision.')
    serialized = json.dumps(receipt, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(serialized)
    print(serialized, end='')


if __name__ == '__main__':
    main()
