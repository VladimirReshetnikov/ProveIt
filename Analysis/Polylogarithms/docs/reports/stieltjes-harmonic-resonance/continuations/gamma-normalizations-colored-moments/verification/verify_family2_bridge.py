#!/usr/bin/env python3
"""Exact, noncircular reconciliation of the printed Family 2 RHS.

Keep verify_depth_two.py alongside this file. Only Python's standard
library is required. The original Family 2 equality is not an input.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import verify_depth_two as v


def multiply(a, b):
    out = {}
    for x, cx in a.items():
        for y, cy in b.items():
            key = tuple(i+j for i, j in zip(x, y))
            out[key] = out.get(key, Q(0)) + cx*cy
    return {key: c for key, c in out.items() if c}


def main():
    rows = [
        (1, -9, v.distribution((3,), (0,))),
        (2, 18, v.distribution((3,), (2,))),
        (4, -12, v.distribution((2, 1), (2, 2))),
        (5, -96, v.shuffle_residual(1, 0)),
        (9, -24, v.multiply_by_single(v.distribution((2,), (0,)), 1, 1)),
        (10, 6, v.distribution((2, 1), (0, 2))),
        (13, -12, v.distribution((1, 2), (2, 2))),
        (14, 6, v.distribution((1, 2), (2, 0))),
        (15, 12, v.multiply_by_single(v.distribution((1,), (2,)), 2, 2)),
    ]
    delta = v.add(*[(sx*sy, v.single_product(1, x, 2, y))
                   for x, sx in ((1, 1), (3, -1))
                   for y, sy in ((1, 1), (3, -1))])
    target = v.real(v.add((96, v.li((1, 2), (1, 0))),
                         (87, v.li((3,), (0,))), (24, delta),
                         (6, v.single_product(2, 0, 1, 2))))
    certificate = v.real(v.add(*[(c, row) for _, c, row in rows]))
    residual = v.add((1, target), (-1, certificate))
    assert residual == {}, residual
    assert all(v.check_admissible(row) for _, _, row in rows)

    # Formal polynomials in Z=zeta(3), P=pi, G=Catalan, L=log(2).
    Z = {(1, 0, 0, 0): Q(1)}
    P = {(0, 1, 0, 0): Q(1)}
    G = {(0, 0, 1, 0): Q(1)}
    L = {(0, 0, 0, 1): Q(1)}
    P2, L2 = multiply(P, P), multiply(L, L)
    PG, P2L = multiply(P, G), multiply(P2, L)
    mu2 = v.add((Q(5, 96), P2), (-Q(1, 8), L2))
    lam2 = v.add((1, G), (-Q(1, 8), multiply(P, L)))
    h11 = v.add((Q(1, 8), L2), (-Q(1, 32), P2))
    h12 = v.add((-Q(29, 32), Z), (Q(1, 4), PG), (Q(1, 96), P2L))
    printed_rhs = v.add((3, Z), (-4, multiply(L, mu2)),
                       (-1, multiply(P, lam2)), (-4, multiply(L, h11)),
                       (3, h12))
    evaluated_lhs = v.add((Q(9, 32), Z), (-Q(1, 4), PG), (Q(7, 96), P2L))
    bridge_residual = v.add((1, printed_rhs), (-1, evaluated_lhs))
    assert bridge_residual == {}, bridge_residual
    report = {
        'status': 'PASS',
        'strict_convention': 'Li_ab(u,v)=sum_{n>m>0} u^n*v^m/(n^a*m^b)',
        'h12_definition': 'Re Li_12(i,1)',
        'h12_relation_rows': [{'original_row': j, 'coefficient': str(c)}
                              for j, c, _ in rows],
        'h12_expanded_target': v.encoded(target),
        'h12_exact_residual': v.encoded(residual),
        'h12_coefficients': {'zeta(3)': '-29/32', 'pi*Catalan': '1/4',
                             'pi^2*log(2)': '1/96'},
        'printed_rhs_exact_residual': bridge_residual,
        'printed_rhs_coefficients': {'zeta(3)': '9/32', 'pi*Catalan': '-1/4',
                                     'pi^2*log(2)': '7/96'},
        'uses_printed_equality_as_input': False,
        'uses_numerical_recognition': False,
    }
    output = (Path(__file__).resolve().parent.parent / 'evidence' / 'family2_bridge_verification.json')
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
