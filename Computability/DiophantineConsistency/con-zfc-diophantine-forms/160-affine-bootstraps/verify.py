#!/usr/bin/env python3
"""Check the release integrity and all finite equation certificates offline."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def manifest_check():
    manifest = ROOT / 'MANIFEST.sha256'
    if not manifest.is_file():
        raise ValueError('release manifest is missing')
    checked = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.resolve().is_relative_to(ROOT) or not path.is_file():
            raise ValueError('invalid manifest path: ' + relative)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError('release digest mismatch: ' + relative)
        checked += 1
    if not checked:
        raise ValueError('empty release manifest')
    return {'files': checked, 'status': 'PASS'}

def run(script, *arguments):
    result = subprocess.run([sys.executable, '-B', str(ROOT / script), *arguments],
                            cwd=ROOT, check=True, text=True, capture_output=True)
    return result.stdout

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rebuild', action='store_true', help='rebuild the 37 equation JSON files in a temporary directory')
    parser.add_argument('--receipt', type=Path, help='optional path outside the frozen package for a JSON receipt')
    args = parser.parse_args()
    if args.receipt and args.receipt.resolve().is_relative_to(ROOT):
        raise ValueError('write a fresh receipt outside the frozen package')
    integrity = manifest_check()
    print('Release integrity: PASS (' + str(integrity['files']) + ' files)', flush=True)
    endpoint = json.loads(run('code/verify_endpoints.py', *(['--rebuild'] if args.rebuild else [])))
    print('Source, frame, integral maps and endpoint coefficients: PASS', flush=True)
    polynomial = json.loads(run('code/audit_polynomials.py'))
    print('Independent collection of all six quartics: PASS', flush=True)
    exports = run('code/report_inputs.py', '--check').strip()
    print(exports, flush=True)
    if args.rebuild:
        print('Fresh JSON rebuild: ' + str(endpoint['rebuild']['files']) + ' files byte-identical', flush=True)
    receipt = {'status': 'PASS', 'manifest': integrity, 'endpoints': endpoint,
               'independent_polynomials': polynomial, 'exports': exports,
               'scope': 'Finite artifact integrity and polynomial certificates; unbounded mathematical arguments are in the report.'}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print('All finite checks passed. See the report for the unbounded mathematical proof.', flush=True)

if __name__ == '__main__':
    main()
