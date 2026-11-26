#!/usr/bin/env python3
"""Check Table 3 applicability and the endpoint inequalities using rationals.

Bach--Sorenson, Math. Comp. 65 (1996), Thm. 5.1 and Table 3.
A result at x0 extends up to the top of the same table bin since
(A log(x)+B)/x^(1/6) decreases for log(x)>6, A>0 and B>=0.
"""
from fractions import Fraction as Q
from math import factorial


def exp_bounds(t):
    # All t here are below 60. The first omitted ratio is t/202.
    terms = [t**k / factorial(k) for k in range(201)]
    lo = sum(terms)
    return lo, lo + terms[-1]*t/201 / (1 - t/202)


def main():
    x0 = 31 * 10**19
    top = 25 * 10**24
    assert exp_bounds(Q(47))[1] < x0
    assert exp_bounds(Q(59))[0] > top
    assert 100 < 16*47 and 16*59 < 1000
    for degree in (64, 128, 256):
        assert 1000 < (degree//2)*47 and (degree//2)*59 < 10000

    cases = [
        ("1--4", x0, Q(236, 5), 32, 45),
        ("5", x0, Q(236, 5), Q(1745,1000)*16, Q(4,100)*32 + Q(58,10)),
        ("6", x0, Q(236, 5), Q(1257,1000)*32, Q(73,10)),
        ("7", 21*10**21, Q(514,10), Q(1257,1000)*64, Q(73,10)),
        ("8", 22*10**23, Q(561,10), Q(1257,1000)*128, Q(73,10)),
    ]
    for label, x, t, a, b in cases:
        assert exp_bounds(t)[0] > x  # log(x)<t
        bound = a*t+b
        assert 4 * bound**6 < x
        print(f"omega={label}: excludes x >= {x} within the candidate window")


if __name__ == "__main__":
    main()
