#!/usr/bin/env python3
"""Offline regression and deliberate-corruption tests in normal Python and -O.

Default runs the bounded h<=4 verifier twice. --extended checks through h<=6
in both modes. Test outputs must match exactly; every corrupt input must fail.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(flags, arguments):
    return subprocess.run([sys.executable, '-I', '-B', *flags, str(ROOT/'verify.py'), *arguments],
                          cwd=ROOT, text=True, capture_output=True, check=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extended', action='store_true')
    args = parser.parse_args()
    positive_args = ['--json'] + (['--extended'] if args.extended else [])
    positive = []
    for flags in ([], ['-O']):
        passed = run(flags, positive_args)
        require(passed.returncode == 0, f'positive test {flags} failed: {passed.stderr}')
        result = json.loads(passed.stdout)
        require(result['all_checks_passed'] is True, 'missing positive pass marker')
        positive.append(passed.stdout)
    require(positive[0] == positive[1], 'normal and optimized outputs differ')
    original = json.loads((ROOT/'data'/'certificates.json').read_text(encoding='utf-8'))
    mutants = []
    def mutant(label):
        data = copy.deepcopy(original)
        mutants.append((label, data))
        return data['heights'][0]
    mutant('numerator coefficient')['numerator'][1] += 1
    mutant('denominator coefficient')['denominator'][1] += 1
    mutant('recurrence onset')['recurrence_onset'] = 0
    mutant('factor exponent')['factors'][0]['exponent'] += 1
    mutant('reducible claimed factor')['factors'] = [{'coefficients': [1, -4, 4], 'exponent': 1}]
    mutant('Gram determinant')['gram_blocks'][0]['determinant'][1] += 1
    mutant('initial count')['counts_w_1_to_6'][0] += 1
    mutant('state count')['states'] += 1
    mutant('trailing zero')['numerator'].append(0)
    mutant('Boolean coefficient')['denominator'][0] = True
    mutant('dominant coefficient')['alpha'] = '0'
    rejected = 0
    with tempfile.TemporaryDirectory(prefix='report175-guard-tests-') as directory:
        for label, data in mutants:
            path = Path(directory)/'invalid.json'
            path.write_text(json.dumps(data), encoding='utf-8')
            for flags in ([], ['-O']):
                failure = run(flags, ['--max-h', '1', '--data', str(path)])
                require(failure.returncode == 1 and 'VERIFICATION FAILED:' in failure.stderr,
                        f'{label} was not properly rejected in mode {flags}: {failure.stdout} {failure.stderr}')
                rejected += 1
    for flags in ([], ['-O']):
        denied = run(flags, ['--max-h', '6'])
        require(denied.returncode == 2 and 'require explicit --extended' in denied.stderr,
                'extended range was not opt-in')
    print(json.dumps({'all_guard_tests_passed': True,
                      'positive_runs': ['normal', 'optimized (-O)'],
                      'max_h': 6 if args.extended else 4,
                      'identical_positive_output': True,
                      'corrupt_inputs_per_mode': len(mutants),
                      'corrupt_input_rejections': rejected,
                      'explicit_extended_scope_rejections': 2,
                      'self_tests_run_in_both_modes': True}, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f'GUARD TEST FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
