#!/usr/bin/env python3
"""Quick tests, including fresh-output and optimized-mode checks. No assert guards."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import sympy as sp
from coefficients import angular_amplitudes, angular_coefficients, affine_coefficients, log_coefficients
from counts import (KNOWN, stirling_table, stirling_count, santos_counts,
                    board_counts, literal_counts, coefficient_count)
from inverse import formal_inverse_checks
from reproduce import published
from compare_receipts import compare


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def rejects(call, exception=ValueError):
    try:
        call()
    except exception:
        return
    raise RuntimeError('invalid input was not rejected')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, help='optional fresh deterministic receipt directory')
    args = parser.parse_args()
    if args.out is not None and args.out.exists():
        parser.error('--out must name a fresh directory')
    for bad in (-1, True, 1.5, '3'):
        rejects(lambda: angular_amplitudes(bad))
        rejects(lambda: stirling_table(bad))
    rejects(lambda: log_coefficients([]))
    rejects(lambda: log_coefficients([2, 3]))
    rejects(lambda: stirling_count(2, [[1]]))
    expected_P, expected = published()
    generated = angular_amplitudes(4)
    require(len(generated) == 5, 'amplitude generator is not arbitrary order')
    for j in range(4):
        require(sp.expand(generated[j]-expected_P[j]) == 0, 'P data mismatch')
    for order in (0, 1):
        a, ac = angular_coefficients(order)
        b, bc = affine_coefficients(order)
        for p in ac:
            for j in range(order+1):
                require(sp.cancel(ac[p][j]-bc[p][j]) == 0, 'angular/affine mismatch')
                require(sp.cancel(ac[p][j]-expected[p][j]) == 0, 'coefficient data mismatch')
    table = stirling_table(17)
    santos = santos_counts(17)
    for n, value in enumerate(KNOWN):
        require(stirling_count(n, table) == santos[n] == value, 'known count mismatch')
    for n in range(6):
        board = board_counts(n)
        require(literal_counts(n) == board, 'all-k literal board mismatch')
        require(coefficient_count(n) == board[n] == KNOWN[n], 'coefficient identity mismatch')
    inverse = formal_inverse_checks(expected)
    require(inverse['vanishing_residual_powers'] == [0, 1, 2, 3], 'inverse coverage mismatch')
    here = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='bishop-tests-') as temp:
        a, b = Path(temp)/'normal', Path(temp)/'optimized'
        common = [str(here/'reproduce.py'), 'counts', '--max-n', '5', '--board-max', '5',
                  '--literal-max', '5', '--coefficient-max', '5']
        subprocess.run([sys.executable, *common, '--out', str(a)], check=True)
        subprocess.run([sys.executable, '-O', *common, '--out', str(b)], check=True)
        compare(a, b)
        fail = subprocess.run([sys.executable, *common, '--out', str(a)], capture_output=True)
        require(fail.returncode != 0, 'existing output directory was not rejected')
        compare(a, b)
        # Semantic comparator must reject corrupted receipts, even under -O.
        manifest = json.loads((b/'manifest.json').read_text())
        manifest['status'] = 'FAIL'
        (b/'manifest.json').write_text(json.dumps(manifest))
        rejects(lambda: compare(a, b), ArithmeticError)
    if args.out is not None:
        from reproduce import dump
        args.out.mkdir(parents=True, exist_ok=False)
        dump(args.out/'contracts.json', {
            'status': 'PASS',
            'checks': ['negative and noninteger orders and sizes rejected',
                       'invalid logarithmic series rejected',
                       'short Stirling table rejected',
                       'amplitude generation through order 4',
                       'angular and affine coefficients through order 1',
                       'known exact counts through n=17',
                       'all-k literal and board counts through n=5',
                       'bivariate coefficient identity through n=5',
                       'exact parity-aware inverse residual through order 3',
                       'normal and optimized CLI receipts identical',
                       'existing output directory rejected without alteration',
                       'corrupted semantic receipt rejected']})
        dump(args.out/'manifest.json', {'status': 'PASS', 'schema_version': 1,
             'command': 'test_contracts', 'receipts': ['contracts.json']})
    print('PASS: quick regression, negative-input, fresh-output, inverse, and normal/-O tests')


if __name__ == '__main__':
    main()
