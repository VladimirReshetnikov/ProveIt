#!/usr/bin/env python3
"""Exact routing-budget checks and high-precision evaluations of rate bounds.

The budget comparison uses rational/integer arithmetic only. The displayed
transcendental evaluations use mpmath and are approximations, not directed
interval enclosures. Mathematical inequalities are proved in article.tex.
Run: python3 code/asymptotic_bounds.py
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
import json
from math import comb, factorial
from pathlib import Path
import mpmath as mp


def hash_counts(s: int, R: int) -> list[int]:
    if s < 2 or R < 1:
        raise ValueError('Require s >= 2 and R >= 1.')
    b = s.bit_length()  # exactly ceil(log_2(s+1))
    counts = [1]
    for z in range(2,R+1):
        numerator = z**z * (z*b+1)
        denominator = factorial(z)
        counts.append(-(-numerator//denominator))
    return counts


def canonical_R(s: int) -> int:
    R = 1
    f = 2
    while f < s:
        R += 1
        f *= R+1
    return R


def budget_bound(q: int, s: int, m: int, R: int) -> Fraction:
    """A conservative rational upper bound for the required residue count."""
    if not q > 2 or not 1 <= R < m <= s:
        raise ValueError('Require q > 2 and 1 <= R < m <= s.')
    t = q-1
    main = sum((Fraction(comb(m,z),(s*t)**(z-1)) for z in range(1,R+1)), Fraction())
    tail = Fraction(comb(m,R+1),s**R)
    return main+tail+sum(hash_counts(s,R))+1


def largest_certified_block(q: int, s: int) -> tuple[int,int,Fraction]:
    best = None
    for R in range(1,canonical_R(s)+1):
        lo,hi = R+1,s
        if lo > hi or budget_bound(q,s,lo,R) > s:
            continue
        while lo < hi:
            mid = (lo+hi+1)//2
            if budget_bound(q,s,mid,R) <= s:
                lo = mid
            else:
                hi = mid-1
        B = budget_bound(q,s,lo,R)
        if best is None or lo > best[0]:
            best = lo,R,B
    if best is None:
        raise ValueError('This conservative sufficient criterion certifies no block.')
    return best


def row(q: int,s: int) -> dict:
    t = q-1
    m,R,B = largest_certified_block(q,s)
    gamma = mp.log(t)/mp.log(mp.mpf(q)/t)
    c = t*mp.log(mp.mpf(q)/t)
    F = t-(t-1)*mp.exp(m*mp.log1p(mp.mpf(1)/(s*t)))
    if F <= 0:
        raise ArithmeticError('Unexpected nonpositive exact-optimum factor.')
    lower_centered = s*t*mp.expm1(-gamma*mp.log1p(mp.mpf(1)/(s*t)))+gamma
    upper_centered = s*t*mp.expm1(mp.log(F)/m)+gamma
    return {'q': q, 's': s, 'm': m, 'R': R,
            'rational_budget_numerator': str(B.numerator),
            'rational_budget_denominator': str(B.denominator),
            'budget_verified_le_s': B <= s,
            'm_over_s_approx': mp.nstr(mp.mpf(m)/s,16),
            'critical_c_approx': mp.nstr(c,18),
            'gamma_approx': mp.nstr(gamma,18),
            'lower_centered_error_approx': mp.nstr(lower_centered,16),
            'upper_centered_error_approx': mp.nstr(upper_centered,16)}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='results/asymptotic_bounds.json')
    args=parser.parse_args()
    mp.mp.dps=90
    rows=[row(q,10**k) for q in (3,4,5) for k in (3,6,9,12,18)]
    for r in rows:
        print(r['q'],r['s'],r['m'],r['R'],
              r['lower_centered_error_approx'],r['upper_centered_error_approx'])
    output=Path(args.output)
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps({'evaluation_digits':90,
        'decimal_status':'approximations; no certified decimal directions',
        'budget_status':'all comparisons exact rational arithmetic', 'rows':rows},indent=2)+'\n')
    with output.with_suffix('.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)

if __name__ == '__main__':
    main()
