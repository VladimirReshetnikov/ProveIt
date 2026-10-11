#!/usr/bin/env python3
"""Reproduce the packaged exact checks or the complete diagnostic suite."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT/'code'


def run(name, *args):
    print('\nRunning ' + name, flush=True)
    result = subprocess.run([sys.executable, str(CODE/name), *map(str, args)], cwd=ROOT)
    if result.returncode:
        raise SystemExit(result.returncode)


def exact():
    run('differential_normal_form.py')
    run('mixed_sixth.py')
    run('verify_normal_form_sectors.py')
    # Keep the supplied full diagnostic record intact in exact-only mode.
    import verify_adjacent_tail_prefix as tail
    record = tail.exact_checks()
    (ROOT/'verification/adjacent_tail_exact.json').write_text(json.dumps(record, indent=2)+'\n')
    print('Adjacent-tail exact assertions:', record.get('exact_assertions', 'passed'), flush=True)
    from audit_mixed_sixth import exact_audit
    mixed = exact_audit()
    (ROOT/'verification/mixed_sixth_exact.json').write_text(json.dumps(mixed, indent=2)+'\n')
    print('Mixed-coordinate exact audit:', mixed, flush=True)


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--exact', action='store_true')
    mode.add_argument('--full', action='store_true')
    args = parser.parse_args()
    exact()
    if args.full:
        run('verify_bicolored_parity.py')
        run('verify_adjacent_tail_prefix.py', '--numeric')
        run('verify_derivative_polynomial_spectral.py', '--output',
            ROOT/'verification/derivative_polynomial_spectral.json')
        run('verify_hurwitz_products.py')
        run('audit_mixed_sixth.py', '--dps', 115, '--n', 100, '--order', 80)
        run('verify_sixth_moment.py')
    print('\nRequested verification suite completed.', flush=True)


if __name__ == '__main__':
    main()
