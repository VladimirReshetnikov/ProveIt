#!/usr/bin/env python3
"""Exact-arithmetic unit tests and deliberate local-certificate corruptions."""
import argparse
import copy
import json
import random
from fractions import Fraction as F
from pathlib import Path
import rigorous as r
import certify_local as local
from certify_consequences import inverse_certificate, remainder_certificate
from test_rational_circle import naive_determinant


def enclose(interval, values, label):
    r.require(all(F(interval.lo, r.S) <= value <= F(interval.hi, r.S) for value in values),
              label + ' does not enclose exact endpoints')


def rejected(label, function, fragment):
    try:
        function()
    except ArithmeticError as error:
        r.require(fragment in str(error), label + ': wrong rejection')
        return {'test': label, 'result': 'rejected', 'reason': str(error)}
    raise ArithmeticError(label + ': corruption was accepted')


def run(data_dir):
    tests = []
    rng = random.Random(183394326)
    for _ in range(300):
        a, b = sorted([F(rng.randrange(-100, 101), rng.randrange(1, 51)) for _ in range(2)])
        c, d = sorted([F(rng.randrange(-100, 101), rng.randrange(1, 51)) for _ in range(2)])
        ia = r.IV(r.IV(a).lo, r.IV(b).hi, True)
        ib = r.IV(r.IV(c).lo, r.IV(d).hi, True)
        enclose(ia+ib, [a+c, b+d], 'addition')
        enclose(ia-ib, [a-d, b-c], 'subtraction')
        enclose(ia*ib, [x*y for x in (a, b) for y in (c, d)], 'multiplication')
        if not ib.lo <= 0 <= ib.hi:
            enclose(ia/ib, [x/y for x in (a, b) for y in (c, d)], 'division')
        for k in range(5):
            enclose(ia**k, [a**k, b**k], 'power')
    tests.append({'test': 'dyadic arithmetic versus exact rational endpoints', 'cases': 300, 'result': 'PASS'})
    for size in range(1, 5):
        for _ in range(12):
            # Strict diagonal dominance avoids interval uncertain-pivot rejection.
            a = [[rng.randrange(-2, 3) for _ in range(size)] for _ in range(size)]
            for i in range(size):
                a[i][i] = 20
            determinant = r.determinant([[r.IV(v) for v in row] for row in a])
            enclose(determinant, [F(naive_determinant(a))], 'determinant')
    tests.append({'test': 'interval elimination versus independent Leibniz determinant', 'cases': 48, 'result': 'PASS'})
    tests.append(rejected('interval division containing zero', lambda: r.IV(1)/r.IV(-1, 1, True), 'crosses zero'))
    tests.append(rejected('reversed interval endpoints', lambda: r.IV(2, 1, True), 'reversed'))
    tests.append(rejected('uncertain determinant pivot', lambda: r.determinant([[r.IV(0)]]), 'uncertain'))
    tests.append(rejected('noncontractive tail radius', lambda: r.tail_bounds(20, r.IV(1)), 'radius'))

    proposals = json.loads((data_dir/'inverse_proposals.json').read_text())['proposals']
    z = r.IV(local.Z_LOW)
    _, a = r.matrix(20, z, 'L')
    zero = copy.deepcopy(proposals['L_low'])
    zero['dyadic_point_matrix'] = [['0' for _ in row] for row in zero['dyadic_point_matrix']]
    tests.append(rejected('zero inverse point proposal', lambda: r.inverse_bound(a, zero), 'residual'))
    altered = copy.deepcopy(proposals['L_low'])
    altered['dyadic_point_matrix'][0][0] = str(1000*r.S)
    tests.append(rejected('one corrupted inverse entry', lambda: r.inverse_bound(a, altered), 'residual'))
    wrong_precision = copy.deepcopy(proposals['L_low'])
    wrong_precision['scale_bits'] -= 1
    tests.append(rejected('wrong inverse precision', lambda: r.inverse_bound(a, wrong_precision), 'precision'))
    tests.append(rejected('inverse proposal for wrong endpoint',
                          lambda: r.inverse_bound(a, proposals['L_high']), 'different interval matrix'))
    wrong_size = copy.deepcopy(proposals['L_low'])
    wrong_size['dyadic_point_matrix'].pop()
    tests.append(rejected('truncated inverse matrix', lambda: r.inverse_bound(a, wrong_size), 'dimensions'))

    # Exercise every published numeric consequence with true local outputs and
    # exactly the conservative, independently global-verified constants.
    actual_local = local.run(data_dir)
    global_bounds = {'status': 'PASS', 'z_majorant_radius': '4/5', 'q_circle_radius': '63/100',
                     'Schur': {'inverse_strict_upper': '1575/4', 'B_strict_upper': '27/1000',
                               'C_strict_upper': '21/1000', 'D_strict_upper': '1/50'}}
    remainder = remainder_certificate(global_bounds, actual_local)
    inverse_certificate(actual_local, remainder)
    wider_amplitude = copy.deepcopy(actual_local)
    wider_amplitude['residue']['asymptotic_amplitude']['lo'] = '0'
    tests.append(rejected('amplitude no longer positive enough',
                          lambda: inverse_certificate(wider_amplitude, remainder), 'amplitude endpoints'))
    larger_remainder = dict(remainder, remainder_constant='2500000000')
    tests.append(rejected('oversized remainder breaks threshold at 600',
                          lambda: inverse_certificate(actual_local, larger_remainder), 'positivity threshold'))
    unstable_global = copy.deepcopy(global_bounds)
    unstable_global['Schur']['inverse_strict_upper'] = '100000'
    tests.append(rejected('noncontractive global Schur bound',
                          lambda: remainder_certificate(unstable_global, actual_local), 'Schur contraction'))
    return {'status': 'PASS', 'tests': tests,
            'note': 'Every acceptance guard uses explicit exceptions and survives Python -O.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent.parent/'data')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(args.data_dir), indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
