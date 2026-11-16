#!/usr/bin/env python3
"""Exact rational certificate for B_n < (0.792 n/log(n+1))**n.

The paper proves the universal range n >= 512. This program certifies the
remaining n=1,...,511 by integer arithmetic and rational log enclosures.
It is a reproducibility tool, not an iPRA derivation checker.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import csv
import json

HERE = Path(__file__).resolve().parent
SCALE = 2**40
TERMS = 24


def log_upper_base(z: Q) -> Q:
    """Upper bound for log((1+z)/(1-z)), 0 <= z <= 1/3."""
    assert 0 <= z <= Q(1, 3)
    z2 = z*z
    term = z
    acc = Q(0)
    for j in range(TERMS):
        acc += 2*term/(2*j+1)
        term *= z2
    return acc + 2*term/((2*TERMS+1)*(1-z2))


def ceil_fraction(x: Q) -> int:
    return -(-x.numerator//x.denominator)


def main() -> None:
    bells = [1]
    for n in range(511):
        bells.append(sum(comb(n,k)*bells[k] for k in range(n+1)))
    ln2_upper = log_upper_base(Q(1,3))
    rows = []
    margins = []
    for n in range(1,512):
        m = n+1
        k = m.bit_length()-1
        y = Q(m,2**k)
        z = (y-1)/(y+1)
        u = ceil_fraction(SCALE*(k*ln2_upper+log_upper_base(z)))
        lhs = bells[n]*(125*u)**n
        rhs = (99*n*SCALE)**n
        assert lhs < rhs, (n, u)
        # This margin is itself an exact rational number, not a float.
        margin = Q(rhs-lhs,rhs)
        margins.append((margin,n))
        rows.append((n, u, SCALE,
                     margin.numerator*10**12//margin.denominator, 10**12))
    # Two fixed rational comparisons used for the infinite ranges.
    assert sum(Q(15,16)**j / factorial(j) for j in range(5)) > Q(250,99)
    assert 16/Q(2**16) + Q(1,16)*(1+Q(1,2**16)) < Q(1,10)
    assert 1+Q(3,10)+Q(3,10)**2/2 > Q(4,3)
    with (HERE/'bound_certificate.csv').open('w',newline='') as f:
        w=csv.writer(f)
        w.writerow(['n','log_upper_numerator','log_upper_denominator',
                    'relative_integer_margin_lower_numerator','relative_integer_margin_lower_denominator'])
        w.writerows(rows)
    # A compact exact global lower bound on the relative certificate margin.
    minimum,minimum_n = min(margins)
    scaled_margin = minimum.numerator*10**12//minimum.denominator
    result = {'status':'PASS','arithmetic':'Python arbitrary-size integers and fractions',
              'finite_range':[1,511],'universal_range_proved_in_paper':'n >= 512',
              'log_series_terms':TERMS,'log_denominator':SCALE,
              'smallest_relative_integer_margin_index':minimum_n,
              'smallest_relative_integer_margin_lower_bound':f'{scaled_margin}/1000000000000',
              'warning':'Finite certificate, not a syntactic iPRA proof checker.'}
    (HERE/'bound_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


def factorial(n: int) -> int:
    a=1
    for k in range(1,n+1):
        a*=k
    return a


if __name__ == '__main__':
    main()
