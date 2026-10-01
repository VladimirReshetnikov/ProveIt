"""Exact classifier for integer targets of the Keller map.

Usage: python code/classify.py A B C
Needs SymPy (tested with 1.14.0). Output is JSON; fractions are strings.
"""
from __future__ import annotations
import argparse
import json
from math import gcd, isqrt
from fractions import Fraction
from arithmetic import (dyadic_condition, odd_obstruction, reconstruct,
                        keller)


def classify(A: int, B: int, C: int) -> dict:
    """Return a certificate using exact integer/rational computations."""
    if not all(isinstance(n, int) and not isinstance(n, bool) for n in (A,B,C)):
        raise TypeError('A, B, and C must be integers.')
    if C == 0:
        point = (0, B, A-4*B*B)
        assert keller(*point) == (A,B,C)
        return {'target': [A,B,C], 'classification': 'integral_image',
                'locally_integral_everywhere': True,
                'boundary_point': list(point)}
    try:
        import sympy as sp
    except ImportError as exc:
        raise RuntimeError('Install SymPy: python -m pip install sympy') from exc
    s = sp.Symbol('s')
    H = sp.Poly(s**3-2*s*s+B*C*s-2*A*C*C, s, domain=sp.QQ)
    roots_dict = sp.polys.polytools.ground_roots(H)
    roots = []
    for a, multiplicity in sorted(roots_dict.items(), key=lambda p: p[0]):
        if a.q != 1:
            raise ArithmeticError('A monic integer cubic has a noninteger rational root.')
        roots.append((int(a), int(multiplicity)))
    u, v = 3*B*C-4, 27*A*C*C-4
    G = gcd(u,v)
    odd = odd_obstruction(A,B,C)
    E = dyadic_condition(A,B,C)
    local = bool(roots) and odd == 1 and E
    points = []
    for a,multiplicity in roots:
        if multiplicity == 1:
            pt = reconstruct(a,A,B,C)
            points.append({'root': a, 'coordinates': [str(z) for z in pt],
                           'integral': all(z.denominator == 1 for z in pt)})
    integral = any(row['integral'] for row in points)
    if integral and not local:
        raise ArithmeticError('Integral point disagrees with local certificate.')
    if len(roots) == 3:
        kind = 'completely_split_distinct'
    elif any(m > 1 for _,m in roots):
        kind = 'repeated_root'
    elif roots:
        kind = 'rational_plus_irreducible_quadratic'
    else:
        kind = 'irreducible_cubic'
    classification = ('integral_image' if integral else
                      'integral_hasse_failure' if local else
                      'not_everywhere_locally_integral')
    result = {
        'target': [A,B,C], 'classification': classification,
        'locally_integral_everywhere': local, 'fiber_kind': kind,
        'H_coefficients': [1,-2,B*C,-2*A*C*C],
        'rational_roots': [{'root':a, 'multiplicity':m} for a,m in roots],
        'gcd_certificate': {'U':u,'V':v,'G':G,'odd_part':odd},
        'dyadic_condition': E, 'rational_fiber': points}
    if kind == 'rational_plus_irreducible_quadratic':
        a = roots[0][0]
        Delta = -3*a*a+4*a+4-4*B*C
        assert Delta < 0 or isqrt(Delta)**2 != Delta
        result['quadratic_discriminant'] = Delta
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('A',type=int)
    parser.add_argument('B',type=int)
    parser.add_argument('C',type=int)
    args = parser.parse_args()
    try:
        answer = classify(args.A,args.B,args.C)
    except (ValueError, TypeError, RuntimeError) as exc:
        parser.exit(2, f'Error: {exc}\n')
    print(json.dumps(answer,indent=2))


if __name__ == '__main__':
    main()
