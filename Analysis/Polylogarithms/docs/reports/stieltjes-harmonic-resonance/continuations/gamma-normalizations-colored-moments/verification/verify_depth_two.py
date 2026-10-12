#!/usr/bin/env python3
"""Exact certificate for a strict level-four, weight-three identity.

No PSLQ, numerical relation fitting, or external word-algebra module is used.
All polynomial arithmetic uses fractions.Fraction. Colors are exponents of i;
an index tuple ((a,p),(b,q)) means sum_{n>m>0} i^(p*n+q*m)/(n^a*m^b).
The optional quadrature is only an independent diagnostic, never the proof.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse
import json


def add(*terms):
    out = defaultdict(Q)
    for scale, poly in terms:
        for key, value in poly.items():
            out[key] += Q(scale) * value
    return {key: value for key, value in out.items() if value}


def li(weights, colors):
    return {tuple(zip(weights, (c % 4 for c in colors))): Q(1)}


def real(poly):
    """Pass to the formal real quotient L(colors)=L(-colors)."""
    out = defaultdict(Q)
    for key, value in poly.items():
        conjugate = tuple((weight, -color % 4) for weight, color in key)
        out[min(key, conjugate)] += value
    return {key: value for key, value in out.items() if value}


def single_product(s, x, t, y):
    """Strict stuffle product of two single polylogarithms."""
    return add((1, li((s, t), (x, y))),
               (1, li((t, s), (y, x))),
               (1, li((s + t,), (x + y,))))


def shuffle_residual(x, y):
    """R(i^x,i^y) from the six-term identity in the TeX section."""
    return add((1, li((1, 2), (x, y - x))),
               (1, li((2, 1), (x, y - x))),
               (1, li((2, 1), (y, x - y))),
               (-1, li((1, 2), (x, y))),
               (-1, li((2, 1), (y, x))),
               (-1, li((3,), (x + y,))))


def distribution(weights, colors):
    """D_weights(i^colors), with each color 0 or 2 and specified square roots."""
    assert all(c in (0, 2) for c in colors)
    depth, weight = len(weights), sum(weights)
    terms = [(1, li(weights, colors))]
    for signs in product((0, 2), repeat=depth):
        roots = tuple(c // 2 + sign for c, sign in zip(colors, signs))
        terms.append((-2 ** (weight - depth), li(weights, roots)))
    return add(*terms)


def multiply_by_single(poly, s, color):
    """Only depth-one polynomials need to be multiplied in this certificate."""
    terms = []
    for key, coefficient in poly.items():
        assert len(key) == 1
        (t, other), = key
        terms.append((coefficient, single_product(t, other, s, color)))
    return add(*terms)


def check_admissible(poly):
    # Every remaining leading-one coordinate has a nontrivial outer color.
    return all(key[0] != (1, 0) for key in poly)


def encoded(poly):
    return [dict(indices=[w for w, _ in key],
                 colors=[c for _, c in key], coefficient=str(value))
            for key, value in sorted(poly.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--numeric', action='store_true')
    parser.add_argument('--output', type=Path,
                        default=(Path(__file__).resolve().parent.parent / 'evidence' / 'depth_two_verification.json'))
    args = parser.parse_args()

    rows = [
        (-15, 'D_3(1)', distribution((3,), (0,))),
        (6, 'D_3(-1)', distribution((3,), (2,))),
        (-24, 'R(1,-1)', shuffle_residual(0, 2)),
        (60, 'D_21(-1,-1)', distribution((2, 1), (2, 2))),
        (96, 'R(i,1)', shuffle_residual(1, 0)),
        (192, 'R(i,-1)', shuffle_residual(1, 2)),
        (12, 'D_21(1,1)', distribution((2, 1), (0, 0))),
        (12, 'R(1,1)', shuffle_residual(0, 0)),
        (-168, 'Li_1(i) D_2(1)',
         multiply_by_single(distribution((2,), (0,)), 1, 1)),
        (90, 'D_21(1,-1)', distribution((2, 1), (0, 2))),
        (96, 'R(i,i)', shuffle_residual(1, 1)),
        (192, 'R(1,i)', shuffle_residual(0, 1)),
        (12, 'D_12(-1,-1)', distribution((1, 2), (2, 2))),
        (42, 'D_12(-1,1)', distribution((1, 2), (2, 0))),
        (-12, 'Li_2(-1) D_1(-1)',
         multiply_by_single(distribution((1,), (2,)), 2, 2)),
    ]
    delta_product = add(*[(sx * sy, single_product(1, x, 2, y))
                           for x, sx in ((1, 1), (3, -1))
                           for y, sy in ((1, 1), (3, -1))])
    target = real(add((96, li((1, 2), (1, 1))),
                      (-96, li((2, 1), (1, 1))),
                      (-27, li((3,), (0,))),
                      (-24, delta_product),
                      (42, single_product(2, 0, 1, 2))))
    certificate = real(add(*[(coefficient, row)
                             for coefficient, _, row in rows]))
    residual = add((1, target), (-1, certificate))
    assert all(check_admissible(row) for _, _, row in rows)
    assert check_admissible(target)
    assert residual == {}, residual

    # Exact evaluation of the formal target after the known single values:
    # delta_1=i*pi/2, delta_2=2*i*G; Li_2(1)=pi^2/6;
    # Li_1(-1)=-log(2). Hence T=96*A-96*B-27*zeta(3)+24*pi*G-7*pi^2*log(2).
    assert Q(27, 96) == Q(9, 32)
    assert Q(24, 96) == Q(1, 4)
    assert Q(42, 6 * 96) == Q(7, 96)
    report = {
        'status': 'PASS',
        'proof_kind': 'exact rational shuffle/distribution certificate',
        'convention': 'strict n>m; colors i^(p*n+q*m); outer index first',
        'row_count': len(rows),
        'all_row_coordinates_convergent': True,
        'exact_residual': encoded(residual),
        'expanded_target': encoded(target),
        'rows': [dict(coefficient=str(c), relation=name,
                      expanded_real_relation=encoded(real(row)))
                 for c, name, row in rows],
        'rhs_coefficients': {'zeta(3)': '9/32', 'pi*Catalan': '-1/4',
                             'pi^2*log(2)': '7/96'},
    }
    if args.numeric:
        import mpmath as mp
        mp.mp.dps = 80
        # Each integral is derived directly from the strict nested definition.
        a = mp.re(mp.quad(lambda t: 1j * mp.polylog(2, -t) / (1 - 1j*t), [0, 1]))
        b = -mp.quad(lambda t: t * mp.log(t) * mp.log(1+t) / (1+t*t), [0, 1])
        rhs = Q(9, 32).numerator / mp.mpf(Q(9, 32).denominator) * mp.zeta(3)
        rhs -= mp.pi * mp.catalan / 4
        rhs += 7 * mp.pi**2 * mp.log(2) / 96
        report['numeric_diagnostic_not_proof'] = {
            'working_decimal_precision': mp.mp.dps,
            'real_Li_12_i_i': mp.nstr(a, 75),
            'real_Li_21_i_i': mp.nstr(b, 75),
            'difference': mp.nstr(a-b, 75),
            'rhs': mp.nstr(rhs, 75),
            'absolute_residual': mp.nstr(abs(a-b-rhs), 8),
            'rigorous_enclosure': False,
        }
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in
                      ('status', 'row_count', 'all_row_coordinates_convergent',
                       'exact_residual', 'rhs_coefficients')}, indent=2))
    print('Report:', args.output)


if __name__ == '__main__':
    main()
