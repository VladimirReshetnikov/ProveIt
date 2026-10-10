#!/usr/bin/env python3
"""Independent SymPy replay of the Euler polynomial certificates.

This program does not import the producer's polynomial or Bernstein code.
It reconstructs the rational kernel identities symbolically, verifies the
saved dyadic boxes form a partition, and recomputes every Bernstein
coefficient from an independently expanded affine substitution.
"""

from itertools import combinations, product
from pathlib import Path
import json
import sympy as s


def main():
    root = Path(__file__).resolve().parents[1]
    source = root / 'data/euler_polynomial_certificate.json'
    certificate = json.loads(source.read_text())
    x, y, t = s.symbols('x y t')
    expressions = {}
    for n in (2, 3):
        numerator = ((1-x*y*y)**n*(1+x)
                     -(1-x)**n*(1+x*y*y))
        quotient, remainder = s.div(numerator, 1-y, y)
        assert s.expand(remainder) == 0
        expressions[f'P_{n}'] = (s.Poly(
            s.expand(9*(1+x)*(1+x*y*y)-8*quotient), x, y), (x, y))
    numerator = 9*(1-t**8)**3-8*(1-t**3)**3*(1+t**3)**4
    quotient, remainder = s.div(numerator, (1-t)**3, t)
    assert remainder == 0
    expressions['Q_4'] = (s.Poly(quotient, t), (t,))
    reports = []
    for row in certificate['results']:
        polynomial, symbols = expressions[row['name']]
        stored = s.Poly(sum(s.Rational(e['coefficient'])*s.prod(
            z**power for z, power in zip(symbols, e['exponents']))
            for e in row['polynomial']), *symbols)
        assert polynomial == stored
        boxes = [tuple((s.Rational(lo), s.Rational(hi))
                       for lo, hi in c['box']) for c in row['cells']]
        assert all(0 <= lo < hi <= 1 for box in boxes for lo, hi in box)
        for left, right in combinations(boxes, 2):
            assert any(max(a, c) >= min(b, d)
                       for (a, b), (c, d) in zip(left, right))
        assert sum(s.prod(hi-lo for lo, hi in box) for box in boxes) == 1
        degree = polynomial.degree_list()
        minima = []
        count = 0
        for cell, box in zip(row['cells'], boxes):
            replacement = {z:lo+(hi-lo)*z
                           for z, (lo, hi) in zip(symbols, box)}
            local = s.Poly(polynomial.as_expr().subs(
                replacement, simultaneous=True).expand(), *symbols)
            bernstein = []
            for index in product(*(range(d+1) for d in degree)):
                value = s.Rational(0)
                for powers, coefficient in local.terms():
                    if all(j <= i for j, i in zip(powers, index)):
                        value += coefficient*s.prod(
                            s.binomial(i, j)/s.binomial(d, j)
                            for i, j, d in zip(index, powers, degree))
                assert value > 0
                bernstein.append(value)
            assert min(bernstein) == s.Rational(cell['minimum_bernstein_coefficient'])
            assert len(bernstein) == cell['coefficient_count']
            minima.append(min(bernstein))
            count += len(bernstein)
        assert len(boxes) == row['cell_count']
        assert count == row['coefficient_count']
        assert min(minima) == s.Rational(row['minimum_coefficient'])
        reports.append(dict(name=row['name'], boxes=len(boxes),
                            coefficients=count, minimum=str(min(minima))))
    result = dict(status='PASS', producer_imported=False,
                  symbolic_kernel_identities='exact',
                  partition_coverage='exact, including pairwise interior disjointness',
                  reports=reports)
    target = root / 'data/euler_independent_review.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
