#!/usr/bin/env python3
"""Exact, finite checks accompanying the omnific continued-fraction article.

These checks do not implement No, prove an infinite fiber theorem, certify
novelty, or replace the written proofs. Python 3.10+; SymPy 1.12+.
Run: python code/verify.py --output audits/verification.json
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
import json
from pathlib import Path
import random
import sys
import sympy as sp

COUNTS: Counter[str] = Counter()

def check(ok: bool, category: str, context: object = None) -> None:
    if not ok:
        raise AssertionError(f"{category}: {context!r}")
    COUNTS[category] += 1


def continuants(a: list[F]) -> tuple[list[F], list[F]]:
    pm2, pm1, qm2, qm1 = F(0), F(1), F(1), F(0)
    ps, qs = [], []
    for digit in a:
        p, q = digit * pm1 + pm2, digit * qm1 + qm2
        ps.append(p); qs.append(q)
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
    return ps, qs


def evaluate(a: list[F], tail: F) -> F:
    for digit in reversed(a):
        tail = digit + 1 / tail
    return tail


def rational_checks(rng: random.Random) -> None:
    for case in range(700):
        size = rng.randrange(4, 13)
        a = [F(rng.randrange(-9, 10))]
        a += [F(rng.randrange(1, 10)) for _ in range(size - 1)]
        tail = F(rng.randrange(2, 20)) + F(1, rng.randrange(2, 12))
        ps, qs = continuants(a)
        x = evaluate(a, tail)
        current = x
        last_interval = None
        for n in range(size):
            digit = current.numerator // current.denominator
            check(digit == a[n], 'rational_digit_recovery', (case, n))
            current = 1 / (current - digit)
            pp, qp = (ps[n-1], qs[n-1]) if n else (F(1), F(0))
            det = ps[n] * qp - pp * qs[n]
            check(det == (-1 if n % 2 == 0 else 1), 'continuant_determinant')
            r = ps[n] / qs[n]
            s = (ps[n] + pp) / (qs[n] + qp)
            lo, hi = min(r, s), max(r, s)
            check(lo < x < hi, 'open_cylinder_membership')
            check(hi - lo == 1 / (qs[n] * (qs[n] + qp)), 'cylinder_width')
            check(abs(x-r) == 1 / (qs[n] * (qs[n] * current + qp)),
                  'first_endpoint_distance')
            check(abs(x-s) == (current-1) / ((qs[n]+qp) * (qs[n]*current+qp)),
                  'second_endpoint_distance')
            check(qs[n] >= qp and qs[n] > 0, 'denominator_monotonicity')
            if last_interval:
                check(last_interval[0] <= lo < hi <= last_interval[1], 'nested_cylinders')
            last_interval = (lo, hi)
            if n + 2 < size:
                bound = 1 / (4 * qs[n+2] ** 2)
                check(min(x-lo, hi-x) > bound, 'two_step_buffer')
            f0, f1 = 0, 1
            for k in range(size - n):
                check(qs[n+k] >= f1 * qs[n], 'fibonacci_growth')
                f0, f1 = f1, f0 + f1

# Finite generalized polynomials, with growth exponents in Q.
Poly = dict[F, F]

def add(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, F(0)) + c
        if not r[e]:
            del r[e]
    return r


def scale(p: Poly, c: F) -> Poly:
    return {e: a*c for e, a in p.items() if a*c}


def mul(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for e, a in p.items():
        for f, b in q.items():
            r[e+f] = r.get(e+f, F(0)) + a*b
    return {e: a for e, a in r.items() if a}


def generalized_polynomial_checks(rng: random.Random) -> None:
    one = {F(0): F(1)}
    for case in range(180):
        p2, p1, q2, q1 = {}, one, one, {}
        cumulative = F(0)
        for n in range(7):
            degree = F(rng.randrange(0, 13), 4)
            if degree == 0:
                digit = {F(0): F(rng.randrange(1, 8))}
            else:
                digit = {degree: F(rng.randrange(1, 5)),
                         F(0): F(rng.randrange(-4, 5))}
                if degree > F(1,4):
                    digit[F(1,4)] = F(rng.randrange(-4, 5), 3)
                digit = {e:c for e,c in digit.items() if c}
            p, q = add(mul(digit,p1),p2), add(mul(digit,q1),q2)
            if n:
                cumulative += degree
            check(max(q) == cumulative, 'generalized_polynomial_degree', (case,n))
            check(q[max(q)] > 0, 'positive_leading_denominator')
            determinant = add(mul(p,q1), scale(mul(p1,q),F(-1)))
            check(determinant == {F(0): F(-1 if n%2==0 else 1)},
                  'generalized_polynomial_determinant')
            p2,p1,q2,q1 = p1,p,q1,q
    # The additive support projection used in the proof is not multiplicative.
    root = {F(1,2): F(1)}
    project = lambda p: {e:c for e,c in p.items() if e.denominator == 1}
    check(project(mul(root,root)) != mul(project(root),project(root)),
          'projection_not_multiplicative')


def symbolic_checks() -> None:
    a,b,c,d,z,e,t = sp.symbols('a b c d z e t')
    f = lambda u: (a*u+b)/(c*u+d)
    identity = (a*d-b*c)*e/((c*z+d)*(c*(z+e)+d))
    check(sp.cancel(f(z+e)-f(z)-identity) == 0, 'mobius_difference_identity')
    letters = sp.symbols('b1:5')
    for length in range(1,5):
        M = sp.eye(2)
        for digit in letters[:length]:
            M *= sp.Matrix([[digit,1],[1,0]])
        A,B,C,D = M[0,0],M[0,1],M[1,0],M[1,1]
        check(sp.expand(M.det()-(-1)**length) == 0, 'period_matrix_determinant')
        polynomial = C*t*t+(D-A)*t-B
        check(sp.expand((C*t+D)*t-(A*t+B)-polynomial) == 0,
              'period_fixed_point_polynomial')
    # Laurent expansion of the positive solution of rho^2 - omega*rho - 1 = 0,
    # with t=omega^{-1}. Truncation is checked only to its justified order.
    N = 24
    rho = 1/t + sum((-1)**k * sp.catalan(k) * t**(2*k+1) for k in range(N+1))
    residual = sp.expand(rho*rho-rho/t-1)
    for power in range(0, 2*N+2):
        check(residual.coeff(t,power) == 0, 'catalan_laurent_coefficients', power)
    check(residual.coeff(t,2*N+2) != 0, 'catalan_first_unchecked_residual')
    # A rational translation does not enlarge the field of a quadratic point:
    # the translated polynomial is obtained by Y -> Y-h.
    Y,h = sp.symbols('Y h')
    poly = C*Y*Y+(D-A)*Y-B
    shifted = sp.expand(poly.subs(Y,Y-h))
    check(sp.expand(shifted.subs(Y,t+h)-poly.subs(Y,t)) == 0,
          'quadratic_translation_identity')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    rng = random.Random(20260923)
    rational_checks(rng)
    generalized_polynomial_checks(rng)
    symbolic_checks()
    report = {
        'status': 'passed', 'seed': 20260923,
        'checks': dict(sorted(COUNTS.items())),
        'total_assertions': sum(COUNTS.values()),
        'python_version': sys.version.split()[0], 'sympy_version': sp.__version__,
        'scope': 'Exact finite rational, generalized-polynomial, and symbolic identities only.',
        'not_certified': ['the proper-class or infinite-support theorems',
                          'the complete mathematical proof', 'novelty or priority',
                          'Lean formalization']
    }
    text = json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__ == '__main__':
    main()
