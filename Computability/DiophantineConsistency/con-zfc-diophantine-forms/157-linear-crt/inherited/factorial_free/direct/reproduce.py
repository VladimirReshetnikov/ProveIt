#!/usr/bin/env python3
"""Rebuild the selected fixed equations and run the independent finite audits.

Only the Python standard library is needed.  No optimization search or external
network access is performed.  The unbounded semantic proof is a separate part
of the accompanying report.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = 'factorial_free_affine'
ENDPOINTS = ['factorial_free_affine242_balanced',
             'factorial_free_affine241_balanced']
SOURCE_FILES = ['mutation.json', 'raw_source.json', 'factored_source.json',
                'factorization_certificate.json', 'projected.json',
                'projection_certificate.json', 'translation_certificate.json',
                'equation.json', 'expanded_polynomial.json', 'METRICS.json']
ENDPOINT_FILES = ['certificate.json', 'equation.json',
                  'expanded_polynomial.json', 'METRICS.json']
ALIAS_FILES = ['equation.json', 'expanded_polynomial.json', 'METRICS.json',
               'residuals.txt', 'residuals.tex', 'variables.tsv']


def run(arguments):
    command = [sys.executable, '-B', *map(str, arguments)]
    result = subprocess.run(command, check=True, capture_output=True, text=True)
    return result.stdout


def same(first, second):
    if first.read_bytes() != second.read_bytes():
        raise ValueError('Reproduction differs: ' + str(first))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--skip-parent', action='store_true',
                        help='skip the retained parent audit, already included in the supplied receipt')
    args = parser.parse_args()
    matched = []
    with tempfile.TemporaryDirectory(prefix='conzfc-factorial-free-') as temporary:
        temp = Path(temporary)
        run([ROOT/'build_factorial_free.py', '--square-beta', '--alias-majorant',
             '--affine-base', '--output', temp/SOURCE])
        for name in SOURCE_FILES:
            same(ROOT/SOURCE/name, temp/SOURCE/name)
            matched.append(SOURCE + '/' + name)
        for endpoint in ENDPOINTS:
            run([ROOT/'build_affine.py', '--source', temp/SOURCE/'equation.json',
                 '--certificate', ROOT/endpoint/'certificate.json', '--output', temp])
            for name in ENDPOINT_FILES:
                same(ROOT/endpoint/name, temp/endpoint/name)
                matched.append(endpoint + '/' + name)
    exact_args = [ROOT/'check_factorial_free.py', '--affine-only']
    if args.skip_parent:
        exact_args.append('--skip-parent')
    exact = json.loads(run(exact_args))
    interface = json.loads(run([ROOT/'audit_power_interface.py',
                               ROOT/SOURCE/'raw_source.json']))
    readable = json.loads(run([ROOT/'export_equations.py', '--check']))
    aliases = []
    for alias, endpoint in zip(['principal', 'companion'], ENDPOINTS):
        for name in ALIAS_FILES:
            same(ROOT/alias/name, ROOT/endpoint/name)
            aliases.append(alias + '/' + name)
    report = {
        'status': 'PASS',
        'byte_identical_rebuilt_json_files': matched,
        'byte_identical_alias_files': aliases,
        'independent_exact_audit': exact,
        'independent_power_interface_audit': interface,
        'readable_export_check': readable,
        'principal_equation_sha256': hashlib.sha256(
            (ROOT/'principal/equation.json').read_bytes()).hexdigest(),
        'companion_equation_sha256': hashlib.sha256(
            (ROOT/'companion/equation.json').read_bytes()).hexdigest(),
        'scope': 'Exact finite construction and polynomial data; the unbounded semantic proof is separate.'
    }
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
