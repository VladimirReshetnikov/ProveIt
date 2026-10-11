#!/usr/bin/env python3
"""Run the delivered independent audits and validate their recorded residuals.

Floating-point tolerances are regression gates, not rigorous error enclosures.
Each mathematical proof is in the article. No network access is used.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
RESULTS = ROOT / 'results'
SCRIPTS = [
    'verify_nonlinear.py',
    'exact_collision_coefficients.py',
    'verify_collision.py',
    'verify_stieltjes_collision.py',
    'verify_shifted_height_one.py',
    'verify_triple_frequency.py',
    'verify_weighted_arctangent.py',
]


def validate():
    import mpmath as mp
    import sympy
    def read(name):
        return json.loads((RESULTS / name).read_text())
    gates = []
    def gate(name, condition, **details):
        if not condition:
            raise AssertionError(f'{name}: {details}')
        gates.append(dict(name=name, passed=True, **details))

    d = read('nonlinear_checks.json')
    gate('nonlinear exact checks', d['exact_check_count'] == 213, count=d['exact_check_count'])
    gate('nonlinear numerical checks', d['numerical_check_count'] == 4 and
         mp.mpf(d['max_numerical_absolute_error']) < mp.mpf('1e-32'),
         count=4, maximum_absolute_error=str(d['max_numerical_absolute_error']))

    d = read('exact_collision_coefficients.json')
    count = sum(d['exact_checks'].values())
    gate('collision exact checks', count == 33, count=count)
    for filename, count, tolerance in [
        ('collision_validation.json', 9, '1e-35'),
        ('stieltjes_collision_validation.json', 2, '1e-25'),
    ]:
        d = read(filename)
        maximum = max(mp.mpf(row['relative_residual']) for row in d['checks'])
        gate(filename, len(d['checks']) == count and maximum < mp.mpf(tolerance),
             count=count, maximum_scaled_residual=str(maximum))

    d = read('shifted_height_one_results.json')
    gate('fully shifted harmonic checks', d['count'] == 72 and
         mp.mpf(d['max_absolute_error']) < mp.mpf('1e-45'),
         count=72, maximum_absolute_error=d['max_absolute_error'])
    d = read('triple_frequency_results.json')
    maximum = max(mp.mpf(row['absolute_error']) for row in d['results'])
    gate('triple frequency checks', len(d['results']) == 2 and maximum < mp.mpf('1e-50'),
         count=2, maximum_absolute_error=str(maximum))
    d = read('weighted_arctangent_verification.json')
    gate('weighted primitive checks', d['numeric_check_count'] == 78 and
         mp.mpf(d['maximum_absolute_error']) < mp.mpf('1e-60'),
         count=78, maximum_absolute_error=d['maximum_absolute_error'])
    residual_keys = ['primitive_derivative_residual', 'hyperbolic_addition_residual',
                     'trigonometric_addition_residual', 'F_second_derivative_residual']
    gate('weighted exact differential checks',
         all(d['exact_checks'][key] == '0' for key in residual_keys), count=4)
    gate('exact one-product obstruction', d['exact_checks']['coefficient_discrepancy'] == '1/36')
    return {
        'status': 'all gates passed',
        'numerical_comparisons': 167,
        'exact_nonlinear_checks': 213,
        'exact_collision_checks': 33,
        'exact_weighted_differential_checks': 4,
        'exact_weighted_coefficient_obstruction': True,
        'numerical_checks_are_certified_intervals': False,
        'python': platform.python_version(),
        'mpmath': mp.__version__,
        'sympy': sympy.__version__,
        'gates': gates,
    }


def run_script(name):
    started = time.monotonic()
    log = RESULTS / 'logs' / (Path(name).stem + '.log')
    with log.open('w') as stream:
        process = subprocess.run([sys.executable, str(ROOT / 'code' / name)],
                                 cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    return dict(script=name, returncode=process.returncode,
                elapsed_seconds=round(time.monotonic()-started, 3),
                log=str(log.relative_to(ROOT)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=3)
    parser.add_argument('--validate-only', action='store_true')
    args = parser.parse_args()
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / 'logs').mkdir(exist_ok=True)
    runs = []
    started = time.monotonic()
    if not args.validate_only:
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as executor:
            futures = [executor.submit(run_script, name) for name in SCRIPTS]
            for future in as_completed(futures):
                row = future.result()
                runs.append(row)
                print(json.dumps(row), flush=True)
        failed = [row for row in runs if row['returncode']]
        if failed:
            raise SystemExit('Audit subprocess failed; see the corresponding results/logs file.')
    summary = validate()
    summary['runs'] = sorted(runs, key=lambda row: SCRIPTS.index(row['script']))
    summary['elapsed_seconds'] = round(time.monotonic()-started, 3)
    (RESULTS / 'verification_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(summary['status'] + ': 167 numerical comparisons, 246 nonlinear/collision exact checks, '
          'and the exact weighted differential and coefficient checks.', flush=True)


if __name__ == '__main__':
    main()
