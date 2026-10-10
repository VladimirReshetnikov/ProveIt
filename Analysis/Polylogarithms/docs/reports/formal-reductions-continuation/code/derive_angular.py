"""Exact Lagrange coefficients and independent residuals for angular zeros.

The expansion is asymptotic at every fixed exponential cutoff.  This program
does not assert that the untruncated generalized Dirichlet series converges.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import factorial
from pathlib import Path
import json
import sympy as sp

u = sp.Symbol('u')


@lru_cache(None)
def phi_coeffs(n: int, degree: int):
    """Coefficients of -u sin(n*pi/2-n*u)/sin(2*u), exactly."""
    numerator = [sp.S.Zero] * (degree + 1)
    for j in range(degree + 1):
        numerator[j] = -sp.sin(sp.pi * (n - j) / 2) * sp.Integer(n) ** j / factorial(j)
    denominator = [sp.S.Zero] * (degree + 1)
    for j in range(0, degree + 1, 2):
        denominator[j] = sp.Rational((-1) ** (j // 2) * 2 ** (j + 1), factorial(j + 1))
    result = []
    for j in range(degree + 1):
        result.append(sp.expand((numerator[j] - sum(denominator[k] * result[j-k] for k in range(1, j+1))) / 2))
    return tuple(result)


def poly_product(a, b, degree):
    c = [sp.S.Zero] * (degree + 1)
    for j in range(min(len(a), degree + 1)):
        for k in range(min(len(b), degree + 1 - j)):
            c[j+k] += a[j] * b[k]
    return c


def multisets(cutoff: Fraction):
    def visit(ns, base, start):
        n = start
        while base * Fraction(2, n) > cutoff:
            current = ns + (n,)
            newbase = base * Fraction(2, n)
            yield current, newbase
            yield from visit(current, newbase, n)
            n += 1
    yield from visit((), Fraction(1), 3)


def derive(cutoff):
    result = defaultdict(lambda: sp.S.Zero)
    examined = 0
    for ns, base in multisets(cutoff):
        examined += 1
        if sum(n % 2 for n in ns) % 2 == 0:
            continue
        k = len(ns)
        product = [sp.S.One]
        for n in ns:
            product = poly_product(product, phi_coeffs(n, k-1), k-1)
        scalar = sp.Rational(factorial(k-1), sp.prod(factorial(m) for m in Counter(ns).values()))
        atom = sp.prod(sp.Symbol(f'H{n-1}') for n in ns)
        result[base] += scalar * product[k-1] * atom
    return {q: sp.expand(c) for q,c in result.items() if c != 0}, examined


def series_add(a, b):
    c = dict(a)
    for q,v in b.items():
        c[q] = sp.expand(c.get(q, 0) + v)
        if c[q] == 0:
            del c[q]
    return c


def series_mul(a, b, cutoff):
    c = defaultdict(lambda: sp.S.Zero)
    for q,x in a.items():
        for r,y in b.items():
            if q*r > cutoff:
                c[q*r] += x*y
    return {q:sp.expand(v) for q,v in c.items() if sp.expand(v) != 0}


def residual(expansion, cutoff):
    """Substitute into the original Fourier equation, without using phi."""
    powers = [{Fraction(1): sp.S.One}]
    while True:
        p = series_mul(powers[-1], expansion, cutoff)
        if not p:
            break
        powers.append(p)
    result = {}
    for j in range(1, len(powers), 2):
        scalar = sp.Rational((-1) ** ((j-1)//2) * 2**j, factorial(j))
        result = series_add(result, {q:scalar*v for q,v in powers[j].items()})
    n = 3
    while Fraction(2,n) > cutoff:
        h = sp.Symbol(f'H{n-1}')
        for j,p in enumerate(powers):
            scalar = sp.diff(sp.sin(n*sp.pi/2-n*u), u, j).subs(u, 0) / factorial(j)
            if scalar != 0:
                term = {q*Fraction(2,n): h*scalar*v for q,v in p.items() if q*Fraction(2,n)>cutoff}
                result = series_add(result, term)
        n += 1
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cutoff', default='2/13')
    parser.add_argument('--output', default='angular_coefficients.json')
    args = parser.parse_args()
    cutoff = Fraction(args.cutoff)
    if not 0 < cutoff < 1:
        raise ValueError('cutoff must be between zero and one')
    expansion, examined = derive(cutoff)
    check = residual(expansion, cutoff)
    if check:
        raise ArithmeticError(f'Nonzero Fourier residual: {check}')
    rows = [{'base':str(q), 'coefficient':str(c), 'latex':sp.latex(c)} for q,c in sorted(expansion.items(), reverse=True)]
    data = {'cutoff':str(cutoff), 'meaning':'Keep bases strictly larger than cutoff; remainder O(cutoff**a), uniformly b>0.', 'multisets_examined':examined, 'nonzero_bases':len(rows), 'exact_fourier_residual_terms':len(check), 'rows':rows}
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
