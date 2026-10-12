#!/usr/bin/env python3
"""Replay every delivered verification suite and collect its exact scope.

Run in a copy if you wish to preserve the recorded JSON evidence unchanged.
The --collect-existing option only summarizes existing results; it does not
claim to execute the suites. Numerical diagnostics are not interval proofs.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
import mpmath
import sympy

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
SCRIPTS = ['check_tail_squares.py', 'verify_generator.py', 'verify_extra.py',
           'check_spectral.py', 'verify_rank_refinement.py']


def run_script(name: str) -> dict:
    start = time.monotonic()
    print('Starting ' + name, flush=True)
    subprocess.run([sys.executable, str(ROOT / 'verification' / name)], cwd=ROOT, check=True)
    result = {'script': name, 'status': 'passed', 'elapsed_seconds': round(time.monotonic() - start, 3)}
    print('Completed ' + name, flush=True)
    return result


def collect() -> dict:
    def read(name: str):
        return json.loads((DATA / name).read_text(encoding='utf-8'))

    tail = read('telescoping_verification.json')
    spectral = read('spectral_verification.json')
    cyc = read('cyclotomic_verification.json')
    extra = read('cyclotomic_extra_verification.json')
    rank = read('rank_refinement_checks.json')
    assert tail['status'] == 'passed'
    assert rank['status'] == 'exact checks passed' and rank['full_replay']
    assert tail['exact_assertion_count'] == 96 and tail['diagnostic_count'] == 29
    assert spectral['exact_assertions'] == 194 and spectral['numerical_checks'] == 21
    assert len(cyc) == 5 and len(extra) == 7
    assert all(float(row['absolute_error']) < 1e-45 for row in cyc + extra)
    return {
        'analytic_suite_exact_assertions': 290,
        'numerical_diagnostic_count': 62,
        'numerical_precision_range_decimal_digits': [60, 75],
        'numerical_diagnostics_are_interval_certificates': False,
        'rank_certificate_full_replay': True,
        'rank_numerator_monomials': {order: v['integer_polynomial_terms'] for order, v in rank['families'].items()},
        'open_rank_progressions': {'8': 'b = 8001 mod 16384', '10': 'b = 962 mod 2048'},
        'proof_status': 'Written analytic proofs and exact algebraic certificates; no proof-assistant formalization claim.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1, choices=[1, 2, 3, 4, 5], help='Independent suite processes to run concurrently.')
    parser.add_argument('--collect-existing', action='store_true', help='Summarize existing outputs without rerunning suites.')
    args = parser.parse_args()
    start = time.monotonic()
    if args.collect_existing:
        runs = []
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            runs = list(pool.map(run_script, SCRIPTS))
    result = collect()
    result.update({'status': 'passed', 'mode': 'collected_existing_results' if args.collect_existing else 'executed_all_suites',
        'python': platform.python_version(), 'sympy': sympy.__version__, 'mpmath': mpmath.__version__,
        'suite_runs': runs, 'elapsed_seconds': round(time.monotonic() - start, 3)})
    (DATA / 'verification_summary.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

