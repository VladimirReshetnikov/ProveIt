#!/usr/bin/env python3
"""Fresh symbolic rational polynomial identities and geometric-series constants."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def plus(a, b):
    out = [Q(0)]*max(len(a),len(b))
    for i,x in enumerate(a):
        out[i] += x
    for i,x in enumerate(b):
        out[i] += x
    return out


def times(a, b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] += x*y
    return out


def scale(a, c):
    return [Q(c)*x for x in a]


def minus(a,b):
    return plus(a,scale(b,-1))


def at_shift(a,t):
    return [sum(a[j]*comb(j,i)*t**(j-i) for j in range(i,len(a)))
            for i in range(len(a))]


def choose_poly(r):
    p = [Q(1)]
    for i in range(r):
        p = times(p,[-i,1])
    return scale(p,Q(1,factorial(r)))


def main():
    p = []
    for k in range(5):
        poly = [Q(0)]
        for r in range(k+1):
            poly = plus(poly,scale(times(choose_poly(r),choose_poly(k-r)),1 << (r*(k-r))))
        p.append(poly)
    expected = [[1],[0,2],[0,-1,3],[0,Q(2,3),-5,Q(13,3)],
                [0,Q(-1,2),Q(41,4),Q(-33,2),Q(27,4)]]
    assert p == expected
    P3num = [1,1,3]
    D = [2,-15,13]
    high = minus(scale(times(times([-2,1],[-1,2]),P3num),12),
                 scale(times(times([0,1],[1,1]),D),5))
    four = minus(scale([-2,41,-66,27],27),scale([3,5,-6,13],52))
    merged = minus(times([-1,3],minus(D,scale(P3num,3))),D)
    correction = minus(scale(P3num,39),scale(D,9))
    assert high == [24,-46,101,-146,7]
    assert four == [-210,847,-1470,53]
    assert merged == [-1,30,-71,12]
    assert correction == [21,174,0]
    shifts = dict(high_at_21=at_shift(high,21), four_at_28=at_shift(four,28),
                  merged_at_6=at_shift(merged,6))
    assert all(v>0 for row in shifts.values() for v in row)
    x = Q(1,4)
    geom0,geom1,geom2 = 1/(1-x),x/(1-x)**2,x*(1+x)/(1-x)**3
    f_integer = Q(13,2)+2*((geom0+geom1)-(1+2*x+3*x*x))
    int_second = 1+2*(geom2-x)
    half_second = geom2+geom1+geom0/4
    assert f_integer == Q(481,72) < 8
    assert int_second == Q(107,54) < 2
    assert half_second == Q(41,27) < 2
    x = Q(1,2)
    half_f_sqrt2 = Q(3,2)+x/(1-x)**2+Q(3,2)*x/(1-x)
    assert half_f_sqrt2 == 5 and 2*half_f_sqrt2**2 < 64
    result = dict(status='PASS', sector_polynomial_coefficients=[[str(c) for c in row] for row in p],
                  positive_shift_certificates={k:[str(c) for c in row] for k,row in shifts.items()},
                  H3_correction_numerator=[str(c) for c in correction],
                  gaussian_constants=dict(integer_f=str(f_integer), half_f='5*sqrt(2)',
                                          integer_second=str(int_second), half_second=str(half_second)))
    with (HERE/'evidence/algebra.json').open('x') as f:
        json.dump(result,f,indent=2)
        f.write('\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
