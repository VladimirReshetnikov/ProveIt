#!/usr/bin/env python3
"""Integer certificate for J_4(x)>0 on [1,65536] and beta'(1)<1/4.
The only library calls beyond elementary integer operations are isqrt,
bisect_right and the exact-rational Fraction. No transcendental functions.
"""
from bisect import bisect_right
from fractions import Fraction
from math import isqrt

LIMIT = 2**16
B = 2**48
TERMS = 16


def log_ratio(a, b):
    """Bounds for B log(a/b), where 1<=a/b<=2, via twice arctanh."""
    assert b <= a <= 2*b
    u, v = a-b, a+b
    top, bottom = u, v
    lower = 0
    for j in range(TERMS):
        lower += (2*B*top) // ((2*j+1)*bottom)
        top *= u*u
        bottom *= v*v
    # Each division loses <1. The omitted series is <1 in scaled units.
    assert 2*B*9 < 8*(2*TERMS+1)*3**(2*TERMS+1)
    return lower, lower+TERMS+1


LOG2 = log_ratio(2, 1)


def log_bounds(n):
    e = n.bit_length()-1
    lo, hi = log_ratio(n, 2**e)
    return lo+e*LOG2[0], hi+e*LOG2[1]


def prime_list(bound):
    flags = bytearray(b"\x01")*(bound+1)
    flags[:2] = b"\0\0"
    for p in range(2, isqrt(bound)+1):
        if flags[p]:
            flags[p*p::p] = b"\0"*((bound-p*p)//p+1)
    return [p for p in range(3, bound+1, 2) if flags[p]]


def certify():
    beta_upper = Fraction(0)
    for j in range(1, 16):
        n = 2*j+1
        lo, hi = log_bounds(n)
        beta_upper += Fraction(hi if j%2 else -lo, n*B)
    assert beta_upper < Fraction(1, 4)

    ps = prime_list(4*LIMIT)
    # Prefix sums for C=sum(-chi(p))*log p and E=sum(-chi(p))*log(p)/p;
    # intervals in units of 1/B. Outward rounding of quotients is by //.
    clo, chi, elo, ehi = [0], [0], [0], [0]
    for p in ps:
        lo, hi = log_bounds(p)
        if p%4 == 1:
            lo, hi = -hi, -lo
        clo.append(clo[-1]+lo)
        chi.append(chi[-1]+hi)
        elo.append(elo[-1]+lo//p)
        ehi.append(ehi[-1]-((-hi)//p))

    q_values = ({4, 4*LIMIT} | {p for p in ps if p>=4}
                | {4*p for p in ps if p<=LIMIT})
    # x=q/4. On each complementary interval J is affine in 1/x.
    # q*J = 4*C(x)-C(4x)+q*(E(4x)-E(x)).
    best_lo = None
    for q in sorted(q_values):
        a = bisect_right(ps, q//4)
        b = bisect_right(ps, q)
        num = 4*clo[a]-chi[b]+q*(elo[b]-ehi[a])
        assert num > 0, f"not certified at x={q}/4"
        if best_lo is None or num*best_q < best_lo*q:
            best_lo, best_q = num, q
    # Round down only, to six decimals, for a compact certificate summary.
    digit_bound = (best_lo*10**6)//(best_q*B)
    print("beta'(1) < 1/4 (15-term alternating upper estimate)")
    print(f"Certified {len(q_values)} endpoints and breakpoints on [1,{LIMIT}]")
    print(f"Minimum of computed lower bounds is attained at x={best_q}/4")
    print(f"All real x in the interval satisfy J_4(x) >= {digit_bound}/10^6")


if __name__ == "__main__":
    certify()
