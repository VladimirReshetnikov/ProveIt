#!/usr/bin/env python3
"""Certify C(b) < 57/50 for all b>0 using exact rational arithmetic.

The analytic proof uses the manuscript's theorem b_* in (1,2), the
log-convexity of Gamma(b) C(b), and (log Gamma)'' <= 5/3 on [1,2].
The finite certificate here verifies C(k/10)<1137/1000, k=10,...,20,
using the self-contained scalar-domination Euler enclosure M=5/4. All power bounds
are checked by integer tenth-root inequalities.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json

GRID = 2**160
TERMS = 80


def int_root(n, k):
    if n <= 1:
        return n
    lo = 0
    hi = 1 << ((n.bit_length()+k-1)//k)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    assert lo**k <= n < (lo+1)**k
    return lo


def negative_tenth_power(n, k):
    # floor(GRID * n^(-k/10)), certified with integers.
    if k % 10 == 0:
        value = Q(1, n**(k//10))
        return value, value
    root = int_root(GRID**10 // n**k, 10)
    assert root**10 * n**k <= GRID**10
    assert (root+1)**10 * n**k > GRID**10
    return Q(root,GRID), Q(root+1,GRID)


def axis_euler(k, n=TERMS):
    # b=k/10; c_(2j+1)=H_(2j)^(b), since a=0.
    h_lo = h_hi = Q(0)
    cs = [(Q(0),Q(0))]
    for m in range(1,2*n-1):
        lo,hi = negative_tenth_power(m,k)
        h_lo += lo
        h_hi += hi
        if m % 2 == 0:
            cs.append((h_lo,h_hi))
    assert len(cs) == n
    # Finite binomial-tail formula from the manuscript.
    e_lo = e_hi = Q(0)
    for j,(lo,hi) in enumerate(cs):
        w = Q((-1)**j*sum(comb(n,r) for r in range(j+1,n+1)),2**n)
        if w >= 0:
            e_lo += w*lo
            e_hi += w*hi
        else:
            e_lo += w*hi
            e_hi += w*lo
    # Scalar domination: R_N<=C(b)<5/4, so E_N-(5/4)2^-N < g < E_N; C=-2g.
    c_lo = -2*e_hi
    c_hi = -2*e_lo + Q(5,2)*Q(1,2**n)
    assert c_hi < Q(1137,1000)
    return c_lo,c_hi


def main():
    results = []
    for k in range(10,21):
        lo,hi = axis_euler(k)
        results.append({"b":str(Q(k,10)), "lo":str(lo), "hi":str(hi),
                        "decimal_diagnostic":float((lo+hi)/2),
                        "upper_below_1137_1000":True})
    # Interpolation: exp((5/3)(1/10)^2/8)=exp(1/480)<480/479.
    bound = Q(1137,1000)*Q(480,479)
    assert bound < Q(57,50)
    report = {"arithmetic":"exact integer and Fraction",
              "grid":str(GRID), "Euler_terms":TERMS,
              "scalar_domination_error_budget":"5/4",
              "analytic_interpolation_bound":str(bound),
              "conclusion":"C(b) < 57/50 for every b>0",
              "axis_samples":results}
    out = Path(__file__).with_name("rational_euler_constant_certificate.json")
    out.write_text(json.dumps(report,indent=2)+"\n")
    for result in results:
        print(f"b={result['b']:>4}: C(b) = {result['decimal_diagnostic']:.16f}")
    print(f"Certified all-b upper bound: {bound} < 57/50")
    print(f"Wrote {out.name}")


if __name__ == "__main__":
    main()
