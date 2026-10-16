#!/usr/bin/env python3
"""Reproduce the supplied exact checks; no external Python packages needed."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def integrity():
    manifest = ROOT/'SHA256SUMS'
    if not manifest.exists():
        return {'status': 'not present during package assembly'}
    count = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        path = ROOT/relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise RuntimeError(f'Integrity mismatch: {relative}')
        count += 1
    return {'status': 'PASS', 'files': count}


def run_json(script, *args):
    run = subprocess.run([sys.executable, str(ROOT/script), *map(str, args)], cwd=ROOT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if run.returncode:
        raise RuntimeError(f'{script} failed:\n{run.stdout}\n{run.stderr}')
    return json.loads(run.stdout)


def compare(actual, expected_path, ignored=()):
    expected = json.loads((ROOT/expected_path).read_text())
    actual = dict(actual)
    for key in ignored:
        actual.pop(key, None)
        expected.pop(key, None)
    if actual != expected:
        raise RuntimeError(f'Reproduced result differs from {expected_path}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--no-integrity', action='store_true',
                        help='For intentional edits or rebuilding; all mathematical checks still run.')
    args = parser.parse_args()
    manifest = {'status': 'explicitly skipped'} if args.no_integrity else integrity()
    checks = {}
    for label, script, expected in (
        ('padding', 'code/tail_padding.py', 'results/tail_padding.json'),
        ('seeded_subset_kernel', 'code/seeded_subset_kernel.py', 'results/seeded_subset_kernel.json'),
        ('vacuity_countermodel', 'code/check_vacuity_countermodel.py', 'results/vacuity_countermodel_results.json'),
        ('decoder_bisimulation', 'decoder/verify.py', 'decoder/verification_results.json'),
    ):
        actual = run_json(script)
        compare(actual, expected)
        checks[label] = 'PASS'
    actual = run_json('code/measure_point_subset_bic.py', ROOT/'data/source02_formulas.py')
    compare(actual, 'results/point_subset_bic_metrics.json', ignored=('source_file',))
    checks['template_metrics'] = 'PASS'
    expected_machine = json.loads((ROOT/'machine/results/verification.json').read_text())
    run = subprocess.run([sys.executable, str(ROOT/'machine/verify.py')], cwd=ROOT,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if run.returncode:
        raise RuntimeError(f'Machine audit failed:\n{run.stdout}\n{run.stderr}')
    if json.loads((ROOT/'machine/results/verification.json').read_text()) != expected_machine:
        raise RuntimeError('Machine audit result changed.')
    checks['literal_tables'] = {name: {
        'working_states': row['working_states'],
        'affine_cases': row['affine']['pass'],
        'blank_boot_checked': row['boot'] is not None,
    } for name, row in expected_machine['machines'].items()}
    print(json.dumps({'status': 'PASS', 'integrity': manifest, 'checks': checks,
                      'scope': 'Exact supplied certificates and regressions; machine checks use published register-box contracts. No new kernel proof or sub-254 blank-tape record.'}, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: the supplied checkers use assertions.')
    main()
