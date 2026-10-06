#!/usr/bin/env python3
"""Report219 self-contained, deterministic reproducibility CLI. See README.md."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True)+'\n', encoding='utf-8')


def nonnegative(text):
    value = int(text)
    if value < 0:
        raise argparse.ArgumentTypeError('must be nonnegative')
    return value


def parse_targets(text):
    try:
        values = sorted(set(int(piece) for piece in text.split(',')))
    except ValueError as exc:
        raise argparse.ArgumentTypeError('expected a comma-separated list of integers') from exc
    if not values or any(n < 0 for n in values):
        raise argparse.ArgumentTypeError('targets must be nonnegative integers')
    return values


def published():
    import sympy as sp
    from coefficients import r, x, d
    raw = json.loads((HERE/'coefficients_c0_c3.json').read_text(encoding='utf-8'))
    co = {p: [sp.sympify(v, locals={'r': r}) for v in values] for p, values in raw.items()}
    amp = [sp.sympify(v, locals={'x': x, 'd': d}) for v in json.loads(
        (HERE/'amplitudes_P0_P3.json').read_text(encoding='utf-8'))]
    return amp, co


def check_equal(a, b, context):
    import sympy as sp
    if sp.cancel(a-b) != 0:
        raise ArithmeticError(context)


def coefficients_receipt(order, oracle_order):
    import sympy as sp
    from coefficients import angular_coefficients, affine_coefficients, r
    P, cs = angular_coefficients(order)
    expected_P, expected = published()
    for j in range(min(order, 3)+1):
        check_equal(P[j], expected_P[j], 'published amplitude mismatch at '+str(j))
        for p in cs:
            check_equal(cs[p][j], expected[p][j], 'published coefficient mismatch '+p+':'+str(j))
    for values in (P, *cs.values()):
        for value in values:
            if value.has(sp.Float):
                raise ArithmeticError('inexact floating arithmetic entered the formal generator')
    independent = None
    if oracle_order is not None:
        jmax = min(order, oracle_order)
        altP, alt = affine_coefficients(jmax)
        for value in [*altP, *(v for values in alt.values() for v in values)]:
            if value.has(sp.Float):
                raise ArithmeticError('inexact floating arithmetic entered the affine oracle')
        for j in range(jmax+1):
            check_equal(P[j], altP[j], 'affine amplitude mismatch at '+str(j))
            for p in cs:
                check_equal(cs[p][j], alt[p][j], 'affine coefficient mismatch '+p+':'+str(j))
        independent = {'status': 'PASS', 'order': jmax,
                       'method': 'affine contours, finite products and differences, finite log powers, exponential partitions, independent Gaussian coordinates'}
    parity = None
    if order >= 3:
        check_equal(cs['1/2'][3]-cs['0'][3], r**3/(4*(r+1)), 'parity split mismatch')
        parity = str(sp.factor(cs['1/2'][3]-cs['0'][3]))
    return {'status': 'PASS', 'order': order,
            'method': 'angular contours, logarithmic recurrences, Touchard polynomials, correlated Gaussian recursion',
            'amplitudes': [str(v) for v in P],
            'coefficients': {p: [str(v) for v in values] for p, values in cs.items()},
            'published_data_comparison_through': min(order, 3),
            'independent_oracle': independent, 'c3_odd_minus_even': parity}, cs


def counts_receipt(max_n, targets, all_n, board_max, literal_max, coefficient_max):
    from counts import (KNOWN, stirling_table, stirling_count, santos_counts,
                        board_counts, literal_counts, coefficient_count)
    if all_n and targets is not None:
        raise ValueError('--all-n and --targets are mutually exclusive')
    if targets is not None and any(n > max_n for n in targets):
        raise ValueError('every --targets value must be <= --max-n')
    if literal_max > 6:
        raise ValueError('--literal-max must be <=6; literal enumeration is exponential')
    if literal_max > board_max:
        raise ValueError('--literal-max must be <= --board-max')
    if max(board_max, coefficient_max) > max_n:
        raise ValueError('--board-max and --coefficient-max must be <= --max-n')
    if board_max > 20:
        raise ValueError('--board-max must be <=20; subset inclusion-exclusion is exponential')
    if coefficient_max > 20:
        raise ValueError('--coefficient-max must be <=20; rational bivariate extraction is expensive')
    if all_n:
        selected = list(range(max_n+1))
    elif targets is not None:
        selected = targets
    else:
        standard = [20,21,50,51,100,101,200,201,400,401,599,600,max_n,max(0,max_n-1)]
        selected = sorted({n for n in standard if n <= max_n})
    checked = sorted(set(selected) | set(range(min(max_n, len(KNOWN)-1)+1))
                     | set(range(max(board_max, coefficient_max)+1)))
    # Only trusted computed integers are serialized; large requested N can
    # exceed Python 3.11's default decimal conversion limit.
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    table = stirling_table(max_n)
    santos = santos_counts(max_n)
    rows, exact_values = [], {}
    for n in checked:
        value = stirling_count(n, table)
        if value != santos[n]:
            raise ArithmeticError('Santos/Stirling mismatch at n='+str(n))
        if n < len(KNOWN) and value != KNOWN[n]:
            raise ArithmeticError('reference sequence mismatch at n='+str(n))
        exact_values[n] = value
        text = str(value)
        rows.append({'n': n, 'B_n': text, 'digits': len(text),
                     'sha256_decimal': hashlib.sha256(text.encode('ascii')).hexdigest(),
                     'Santos_vs_Stirling': 'PASS'})
    boards = []
    for n in range(board_max+1):
        values = board_counts(n)
        if values[n] != exact_values[n]:
            raise ArithmeticError('board inclusion-exclusion mismatch at n='+str(n))
        literal = 'not requested'
        if n <= literal_max:
            if literal_counts(n) != values:
                raise ArithmeticError('literal board enumeration mismatch at n='+str(n))
            literal = 'PASS for all 0<=k<=n'
        boards.append({'n': n, 'counts_by_piece_number': [str(v) for v in values],
                       'literal_comparison': literal})
    identities = []
    for n in range(coefficient_max+1):
        if coefficient_count(n) != exact_values[n]:
            raise ArithmeticError('bivariate coefficient identity mismatch at n='+str(n))
        identities.append({'n': n, 'status': 'PASS'})
    return {'status': 'PASS', 'max_n': max_n,
            'comparison_scope': 'every n from 0 to max_n' if all_n else 'exactly the listed n values',
            'Santos_vs_Stirling': rows, 'board_inclusion_exclusion': boards,
            'literal_max': literal_max, 'direct_bivariate_coefficient_identity': identities}, exact_values


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['all', 'coefficients', 'counts', 'inverse', 'diagnostics'])
    parser.add_argument('--out', required=True, type=Path, help='new output directory; must not already exist')
    parser.add_argument('--order', type=nonnegative, default=3, help='arbitrary fixed angular order (default 3); high orders are expensive')
    parser.add_argument('--oracle-order', type=nonnegative, default=3, help='independent affine comparison through min(order,oracle-order)')
    parser.add_argument('--skip-oracle', action='store_true', help='omit affine comparison (explicitly recorded)')
    parser.add_argument('--max-n', type=nonnegative, default=600)
    parser.add_argument('--targets', type=parse_targets, help='comma-separated selected exact count comparison sizes')
    parser.add_argument('--all-n', action='store_true', help='compare direct Stirling and Santos for every 0<=n<=max-n')
    parser.add_argument('--board-max', type=nonnegative, default=12)
    parser.add_argument('--literal-max', type=nonnegative, default=5)
    parser.add_argument('--coefficient-max', type=nonnegative, default=12)
    parser.add_argument('--with-diagnostics', action='store_true', help='include optional non-certified diagnostics in all')
    parser.add_argument('--precision', type=int, default=80, help='diagnostic decimal digits, at least 40')
    args = parser.parse_args(argv)
    if args.out.exists():
        parser.error('--out must name a fresh directory')
    if args.max_n > 10000:
        parser.error('--max-n must be <=10000; the O(N^2) integer table has substantial memory cost')
    if args.precision < 40:
        parser.error('--precision must be at least 40')
    if args.all_n and args.targets is not None:
        parser.error('--all-n and --targets are mutually exclusive')
    # A fresh directory is allocated before computation; failures never leave a PASS manifest.
    args.out.mkdir(parents=True, exist_ok=False)
    results = {}
    try:
        _, cs = published()
        if args.command in ('all', 'coefficients'):
            print('Computing exact angular coefficients'+('...' if args.skip_oracle else ' and affine oracle...'), flush=True)
            results['coefficients'], generated = coefficients_receipt(
                args.order, None if args.skip_oracle else args.oracle_order)
            cs = generated
        if args.command in ('all', 'counts', 'diagnostics'):
            print('Comparing exact count methods...', flush=True)
            results['counts'], exact = counts_receipt(args.max_n, args.targets, args.all_n,
                args.board_max, args.literal_max, args.coefficient_max)
        if args.command in ('all', 'inverse'):
            from inverse import formal_inverse_checks
            results['inverse'] = formal_inverse_checks(cs)
        if args.command == 'diagnostics' or (args.command == 'all' and args.with_diagnostics):
            from inverse import numerical_diagnostics
            eligible = {n: value for n, value in exact.items() if n >= 20}
            if not eligible:
                raise ValueError('numerical diagnostics require at least one checked n>=20')
            results['diagnostics'] = numerical_diagnostics(cs, eligible, args.precision)
        for name, result in results.items():
            dump(args.out/(name+'.json'), result)
        manifest = {'status': 'PASS', 'schema_version': 1, 'command': args.command,
                    'receipts': sorted(name+'.json' for name in results),
                    'scope': 'Finite exact checks and formal algebra; diagnostics, if requested, are not certified.'}
        dump(args.out/'manifest.json', manifest)
    except Exception as exc:
        dump(args.out/'failure.json', {'status': 'FAIL', 'exception': type(exc).__name__, 'message': str(exc)})
        raise
    print('PASS: '+', '.join(sorted(results))+'; receipts in '+str(args.out), flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
