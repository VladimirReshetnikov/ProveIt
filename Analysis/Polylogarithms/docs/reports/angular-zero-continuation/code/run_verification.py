#!/usr/bin/env python3
"""Portable exact verification for the polylogarithm continuation package.

The default run checks mathematical certificates and exact finite algebra.
Floating-point diagnostics run only with --diagnostics and are labelled as such.
Reference data are never overwritten. Use ordinary Python, not python -O.
"""
from __future__ import annotations

import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import importlib
import importlib.metadata
import io
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
from package_io import CODE_DIR, DATA_DIR, write_json_new_or_compare, write_new_or_compare


def invoke(module, function, *args):
    return getattr(importlib.import_module(module), function)(*args)


def run_script(filename, *args):
    command = [sys.executable, str(CODE_DIR / filename), *args]
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run(command, cwd=CODE_DIR, env=environment,
                            check=True, text=True, capture_output=True)
    print(result.stdout, end='')
    if result.stderr:
        print(result.stderr, end='')
    return {'command': f'python code/{filename} ' + ' '.join(args), 'exit_status': 0}


def reference_hashes():
    names = ['s2_exact_certificate.json', 's4_exact_certificate.json',
             'zero_coefficients.json', 'zero_brackets.json',
             'rank_parametrization_receipt.json', 'normal_form_receipt.json',
             'general_level_rank_receipt.json', 'universal_euler_receipt.json',
             'diagnostics.json']
    return {name: hashlib.sha256((DATA_DIR / name).read_bytes()).hexdigest() for name in names}


def code_hashes():
    files = sorted(CODE_DIR.glob('*.py')) + sorted((CODE_DIR / 'upstream').glob('*.py'))
    return {str(path.relative_to(CODE_DIR)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in files}


def numerical_diagnostics():
    report = invoke('diagnostics', 'main')
    return {key: report[key] for key in ['status', 'root_count', 'checks',
            'sharp_lower_endpoint_alpha', 'a1_b_infinity_endpoint_beta']}


def main(argv=None):
    if not __debug__:
        raise RuntimeError('Use ordinary Python: -O disables assertions used by certificate verifiers.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates-only', action='store_true',
                        help='Run the standard-library certificate checks and skip SymPy rank checks')
    parser.add_argument('--diagnostics', action='store_true',
                        help='Also run optional floating-point diagnostics; these are not proof certificates')
    parser.add_argument('--receipt', type=Path, help='Write a new JSON receipt, or compare identical existing bytes')
    parser.add_argument('--log', type=Path, help='Write a new detailed log, or compare identical existing bytes')
    args = parser.parse_args(argv)
    checks = [
        ('S4 exact word certificate', 'exact', lambda: invoke('verify_s4_certificate', 'verify')),
        ('S2 exact word certificate', 'exact', lambda: invoke('prove_s2', 'verify')),
        ('Independent S2/S4 word replay', 'exact',
         lambda: [invoke('independent_s4_replay', 'verify', w) for w in (3, 5)]),
        ('All-order zero coefficient table and finite substitution', 'exact',
         lambda: invoke('all_order_zeros', 'verify_reference')),
        ('Rational angular-zero endpoint certificates', 'exact',
         lambda: invoke('certify_zeros', 'verify_reference')),
        ('Universal Euler interval self-test', 'exact',
         lambda: invoke('universal_euler', 'run_self_test')),
    ]
    if not args.certificates_only:
        checks += [
            ('Level-four kernel parametrization and ranks', 'exact',
             lambda: invoke('verify_rank_parametrization', 'verify')),
            ('Level-four normal forms and even-weight ranks', 'exact',
             lambda: invoke('verify_normal_form', 'verify')),
            ('General-level rank checks', 'exact', lambda: invoke('check_general_level', 'verify')),
        ]
    if args.diagnostics:
        checks.append(('Optional numerical diagnostics', 'diagnostic', numerical_diagnostics))

    before = reference_hashes()
    started = datetime.now(timezone.utc).isoformat()
    results = []
    details = []
    for index, (name, kind, function) in enumerate(checks, 1):
        print(f'[{index}/{len(checks)}] {name} ...', flush=True)
        capture = io.StringIO()
        begin = time.perf_counter()
        try:
            with contextlib.redirect_stdout(capture):
                result = function()
        except Exception:
            captured = capture.getvalue()
            print(captured, end='')
            traceback.print_exc()
            print(f'FAIL: {name}', file=sys.stderr)
            return 1
        elapsed = time.perf_counter() - begin
        results.append({'name': name, 'kind': kind, 'status': 'pass',
                        'elapsed_seconds': round(elapsed, 6), 'result': result})
        details.append(f'=== {name} [{kind}] ===\n{capture.getvalue()}')
        print(f'  PASS ({elapsed:.3f}s)', flush=True)
    after = reference_hashes()
    assert before == after, 'Verification modified reference data'
    versions = {}
    for name in ['sympy', 'mpmath', 'numpy', 'scipy']:
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = None
    receipt = {'status': 'pass', 'started_utc': started,
               'python_version': platform.python_version(), 'package_versions': versions,
               'certificates_only': args.certificates_only,
               'numerical_diagnostics_requested': args.diagnostics,
               'reference_data_unchanged': True, 'reference_sha256': before,
               'code_sha256': code_hashes(), 'checks': results,
               'scope': 'Finite exact certificates and replay checks. General mathematical theorems and remainder estimates are proved in the accompanying article. Numerical diagnostics, when requested, are not proofs.'}
    exact_count = sum(row['kind'] == 'exact' for row in results)
    print(f'PASS: {exact_count} exact verification groups; reference data unchanged.')
    if args.diagnostics:
        print('Optional floating-point diagnostics also passed; they are not proof certificates.')
    if args.receipt:
        write_json_new_or_compare(args.receipt, receipt)
    if args.log:
        write_new_or_compare(args.log, '\n'.join(details))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
