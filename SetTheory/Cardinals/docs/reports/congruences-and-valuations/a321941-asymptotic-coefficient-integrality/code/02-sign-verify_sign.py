#!/usr/bin/env python3
"""Exact checks accompanying the A321941 sign theorem.

Uses only Python standard-library rational arithmetic.  The infinite tail
is proved by analytic inequalities in oeis_research.tex; this program
certifies the finite initial segment and an independent BGG recurrence.
"""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path


def mul(a, b, n):
    c = [F(0) for _ in range(n + 1)]
    for i, ai in enumerate(a[:n+1]):
        if ai:
            for j, bj in enumerate(b[:n-i+1]):
                if bj:
                    c[i+j] += ai*bj
    return c


def coefficients(n):
    q = [F(0) for _ in range(n+1)]
    for m in range(n//2+1):
        q[2*m] = F(1, 4**m*factorial(2*m+1))
    invsqrt = [F(1)]
    for k in range(1, n+1):
        invsqrt.append(-sum((F(k)-F(i, 2))*q[i]*invsqrt[k-i]
                           for i in range(1, k+1))/k)
    tanh = [F(0) for _ in range(n+1)]
    if n:
        tanh[1] = F(1, 4)
    for k in range(2, n+1):
        tanh[k] = -sum(tanh[i]*tanh[k-1-i]
                       for i in range(k))/(4*k)
    exp = [F(1)]
    for k in range(1, n+1):
        exp.append(-sum(i*tanh[i]*exp[k-i]
                        for i in range(1, k+1))/k)
    a = mul(invsqrt, exp, n)
    b = [F(0), F(3, 16)]
    for k in range(2, n+1):
        b.append(b[-1]*F((2*k-3)*(2*k+1), 16*k))
    v = [F(0)] + q[:n]
    power = [F(1)] + [F(0)]*n
    s = power.copy()
    for j in range(1, n+1):
        power = mul(power, v, n)
        for k in range(j, n+1):
            s[k] -= b[j]*power[k]
    h = mul(a, s, n)
    poch = F(1)
    d, r = [], []
    for k, hk in enumerate(h):
        if k:
            poch *= F(2*k-1, 2)
        d.append(poch*hk)
        r.append(d[-1]*64**k)
    return h, d, r, b


def alpha(j, k):
    """BGG (2019), Corollary 15, equation (29)."""
    m = k-j
    tau = F(2*j+1, 2)
    rising = [F(1)]
    for i in range(m+2):
        rising.append(rising[-1]*(tau+i))
    p2, p3 = 2**m, 3**m
    return (
        (-1 + F(3*p2, 2) - 2*p3)*rising[m-1]/factorial(m-1)
        + (7-17*p2+17*p3)*rising[m]/factorial(m)
        + (-13+38*p2-33*p3)*rising[m+1]/factorial(m+1)
        + 6*(1-4*p2+3*p3)*rising[m+2]/factorial(m+2)
    )


def main():
    n = 128
    h, d, r, b = coefficients(n)
    known = [1, -14, 86, -3660, -1042202, -247948260,
             -108448540420, -67825082899288,
             -56771982322924154, -61577812542004343156,
             -84012331763021201187180,
             -140805160243370476949256616,
             -284390871665315095422337087524]
    assert r[:len(known)] == known
    assert all(x.denominator == 1 for x in r)
    assert all(h[k] < 0 for k in range(3, n+1))
    for k in range(1, 65):
        assert 8*k*d[k] == sum(alpha(j, k)*d[j] for j in range(k))
    assert b[16] > 100
    assert all(b[15] > b[j] for j in range(1, 15))
    assert 24*F(12, 23)**16 < F(1, 100)
    assert F(33, 32)**2*F(12, 23) < 1
    assert F(7, 8)+F(3, 200)+F(1, 100) == F(9, 10) < 1
    certificate = {
        "exact_sign_range_required": [3, 31],
        "exact_sign_range_checked": [3, n],
        "independent_BGG_recurrence_range": [1, 64],
        "displayed_OEIS_terms_checked": len(known),
        "b16": str(b[16]),
        "b16_greater_than_100": b[16] > 100,
        "b15": str(b[15]),
        "b15_dominates_earlier_terms": all(b[15] > b[j]
                                           for j in range(1, 15)),
        "far_error_at_32": str(24*F(12, 23)**16),
        "far_error_at_32_less_than_1_over_100":
            24*F(12, 23)**16 < F(1, 100),
        "far_bound_decreases_for_k_at_least_32":
            F(33, 32)**2*F(12, 23) < 1,
        "tail_error_bound": "9/10 < 1 for every k >= 32",
        "r": [int(x) for x in r],
        "heat_coefficients": [str(x) for x in h],
        "ratios_h_over_minus_b": [None] + [str(-h[k]/b[k])
                                           for k in range(1, n+1)],
    }
    out = Path(__file__).with_name("sign_verification.json")
    out.write_text(json.dumps(certificate, indent=2)+"\n")
    print("PASS: exact sign h_k<0 for 3 <= k <=", n)
    print("PASS: independent published BGG recurrence for 1 <= k <= 64")
    print("PASS:", len(known), "displayed OEIS terms")
    print("PASS: b_16 > 100, b_15 > b_j for 1 <= j < 15")
    print("PASS: far bound at 32 < 1/100, decreasing thereafter")
    print("PASS: rational tail bound 9/10 < 1")
    print("Certificate:", out)


if __name__ == "__main__":
    main()
