#!/usr/bin/env python3
"""Reproduce the independent research checks or inspect their saved results."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def report():
    data = ROOT / 'data'
    expected = ['dilation_checks.json', 'harmonic_checks.json', 'trilinear_checks.json',
                'gauss_stieltjes_checks.json', 'exact_coefficients_checks.json']
    for name in expected:
        path = data / name
        if not path.exists():
            raise SystemExit(f'Missing result: data/{name}')
        result = json.loads(path.read_text())
        print(f'\n{name}')
        if 'all_passed' in result:
            print(f"  exact_checks: {len(result.get('checks', []))}; all_passed: {result['all_passed']}")
        if 'checks' in result and name != 'exact_coefficients_checks.json':
            print(f"  recorded_checks: {len(result['checks'])}")
        for key in ('status', 'dps', 'precision_dps', 'working_decimal_digits',
                    'tests', 'passed', 'number_of_mixed_jet_checks',
                    'maximum_absolute_residual', 'largest_absolute_residual',
                    'largest_refinement_change', 'proof_status', 'certification'):
            if key in result:
                print(f'  {key}: {result[key]}')
        if not any(key in result for key in ('status', 'tests', 'passed', 'all_passed')):
            print('  Complete component records are available in this JSON file.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report-only', action='store_true')
    args = parser.parse_args()
    if not args.report_only:
        commands = [
            ['code/check_dilation.py'],
            ['code/check_harmonic.py'],
            ['code/check_trilinear.py', '--digits', '32', '--output', 'data/trilinear_checks.json'],
            ['code/check_gauss_stieltjes.py', '--output', 'data/gauss_stieltjes_checks.json'],
            ['code/exact_coefficients.py', '--output-dir', 'data'],
        ]
        for command in commands:
            print('\nRunning ' + ' '.join(command), flush=True)
            subprocess.run([sys.executable] + command, cwd=ROOT, check=True)
    report()


if __name__ == '__main__':
    main()
