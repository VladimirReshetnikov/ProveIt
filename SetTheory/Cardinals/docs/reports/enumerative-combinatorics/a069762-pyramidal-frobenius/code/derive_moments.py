#!/usr/bin/env python3
"""Generate exact gap-moment quasipolynomials by symbolic finite summation.

Usage: python derive_moments.py --power 1
Requires SymPy. This derives formulas from the proved Apéry set, not interpolation.
The computation grows rapidly with the requested moment order.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s
from verify import K, lifted_apery, gap_moment

n = s.symbols('n')

def sum_powers(length: s.Expr, j: int) -> s.Expr:
    return s.expand((s.bernoulli(j+1,length)-s.bernoulli(j+1,0))/(j+1))

def polynomials(power: int) -> list[s.Expr]:
    if power < 0:
        raise ValueError('power must be nonnegative')
    results = []
    for r in range(6):
        k, ell = K[r], K[(r+1)%6]
        a = n*(n+1)*(2*n+1)/6
        b = (n+1)*(n+2)*(2*n+3)/6
        c = (n+2)*(n+3)*(2*n+5)/6
        d, e = (n+1)/k, (n+2)/ell
        A, B, C = a/d, s.Rational(k*ell,6)*(2*n+3), c/e
        red_sums = []
        for j in range(power+2):
            total = 0
            for v in range(k):
                U = (B-1)/k - (ell*v+k-1)//k
                total += sum(s.binomial(j,t)*A**t*(C*v)**(j-t)
                             *sum_powers(U+1,t) for t in range(j+1))
            if r in (1,2):
                v = 0 if r == 1 else 1
                total += ((A*(B+1)+5*B*v)/k)**j
            red_sums.append(s.factor(total))
        lift_sums = []
        for j in range(power+2):
            total = 0
            for j1 in range(j+1):
                for j2 in range(j-j1+1):
                    j3 = j-j1-j2
                    total += (s.binomial(j,j1)*s.binomial(j-j1,j2)
                              *(d*e)**j1*red_sums[j1]*a**j2*c**j3
                              *sum_powers(e,j2)*sum_powers(d,j3))
            lift_sums.append(s.factor(total))
        value = (sum(s.binomial(power+1,j)*s.bernoulli(j,0)
                     *b**(j-1)*lift_sums[power+1-j] for j in range(power+2))
                 -s.bernoulli(power+1,0))/(power+1)
        value = s.factor(value)
        poly = s.Poly(value,n)
        assert poly.degree() == 5*(power+1)
        assert poly.LC() == s.Rational(1,9**(power+1)*(power+1)*(power+2))
        results.append(value)
    if power <= 3:
        for ni in range(2,13):
            assert results[ni%6].subs(n,ni) == gap_moment(lifted_apery(ni),power)
    return results

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--power',type=int,default=1)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    expressions = polynomials(args.power)
    for r, expression in enumerate(expressions):
        print(f'n mod 6 = {r}: {expression}')
    print('PASS exact degree, leading coefficient, and available numerical checks')
    if args.output:
        args.output.write_text(json.dumps({'power':args.power,
                               'polynomials':[str(p) for p in expressions]},indent=2)+'\n')
