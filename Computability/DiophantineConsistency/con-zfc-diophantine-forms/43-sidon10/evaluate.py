#!/usr/bin/env python3
"""Evaluate the delivered ten-integer polynomial modulo a positive integer.

Example: python3 evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1 1
The positional order is f,g,h,k,l,w,x,y,z,m. Modular vanishing is not an
integer-solution certificate. Evaluation is inexpensive even though the
polynomial's exact integer values can have very many digits.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
from circuit import evaluate

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modulus', type=int, default=1000003)
    parser.add_argument('values', nargs=10, type=int,
                        metavar='INTEGER', help='f,g,h,k,l,w,x,y,z,m in that order')
    args = parser.parse_args()
    if args.modulus < 2:
        parser.error('--modulus must be at least 2')
    modulus = args.modulus
    body = json.loads((ROOT / 'generated/signed10_b2.json').read_text())
    records = json.loads((ROOT / 'generated/source_records.json').read_text())
    binding = json.loads((ROOT / 'data/coefficients_binding.json').read_text())
    ports = {}
    for row in binding['files']:
        packed = (ROOT / 'data' / (row['name'] + '.bin.gz')).read_bytes()
        raw = gzip.decompress(packed)
        if (hashlib.sha256(raw).hexdigest() != row['sha256']
                or hashlib.sha256(packed).hexdigest() != row['gzip_sha256']):
            raise SystemExit('Coefficient payload hash mismatch: ' + row['name'])
        port = {'K': 'K0', 'MF_source': 'MF'}.get(row['name'], row['name'])
        ports[port] = int.from_bytes(raw, 'little') % modulus
    fixed = {}
    for name, recipe in records['recipes'].items():
        value = 0
        for term in recipe:
            coefficient = term['coefficient']
            for port, exponent in zip(records['ports'], term['powers']):
                coefficient = coefficient * pow(ports[port], exponent, modulus) % modulus
            value = (value + coefficient) % modulus
        fixed[name] = value
    fixed['beta_source'] = pow(2, body['source']['beta_exponent'], modulus)
    values = dict(zip(body['variables'], args.values))
    residue, _ = evaluate(body, fixed, values, modulus)
    print(json.dumps({'variables': values, 'modulus': modulus, 'residue': residue,
                      'interpretation': 'Modular evaluation only; not an integer-solution certificate.'},
                     indent=2))


if __name__ == '__main__':
    main()
