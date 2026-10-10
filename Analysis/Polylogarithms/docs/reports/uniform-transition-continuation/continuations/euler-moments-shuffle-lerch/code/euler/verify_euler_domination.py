#!/usr/bin/env python3
"""Independent exact checks for the universal Euler-remainder theorem.

The theorem for every N and every point is proved analytically in the
article. These finite rational checks catch normalization and endpoint
mistakes; they are not offered as a replacement for that proof.

Only the Python standard library is required.
"""
from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path


def phi(n, x):
    return (1 - x)**n / (1 + x)


def f(n, x):
    return x**n / (2 - x)


def check_scalar():
    tests = strict_tests = 0
    for n in (1, 2, 3, 4, 5, 8, 13, 21, 64):
        for ti in range(17):
            t = Q(ti, 16)
            for qi in range(17):
                q = Q(qi, 16)
                lhs = phi(n, q*t) - phi(n, t)
                rhs = (1-q) / (1+q)
                assert 0 <= lhs <= rhs, (n, q, t)
                if 0 < t < 1 and 0 < q < 1:
                    assert lhs < rhs
                    strict_tests += 1
                if t == 1 and 0 < q < 1:
                    assert (lhs == rhs) == (n == 1)
                if t > 0 and q < 1:
                    a, b = 1-q*t, 1-t
                    assert lhs/(a-b) == (f(n,a)-f(n,b))/(a-b)
                    assert rhs/(a-b) == 1/(2-a-b)
                tests += 1
    return {"rational_scalar_checks": tests,
            "strict_interior_checks": strict_tests}


def check_geometric_tail():
    tests = 0
    for xi in range(1, 9):
        x = Q(xi, 8)
        for vi in range(1, 8):
            v = Q(vi, 8)
            d = [((1-x*x)**j-(1-x*x*v*v)**j)/(1-v)
                 for j in range(11)]
            g = -x*x*(1+v)/((1+x*x)*(1+x*x*v*v))
            for n in range(1, 11):
                e = sum((d[j]/2**(j+1) for j in range(n)), Q(0))
                r = (phi(n,x*x*v*v)-phi(n,x*x))/(1-v)
                assert 2**n*(e-g) == r
                assert 0 < r <= (1+v)/(1+v*v)
                if x < 1 or n > 1:
                    assert r < (1+v)/(1+v*v)
                tests += 1
    return {"exact_kernel_and_tail_checks": tests}


def euler_values(a, b, m):
    """Exactly rational for nonnegative integer a, positive integer b."""
    h = Q(0)
    coeff = []
    for n in range(1, 2*m):
        if n % 2:
            coeff.append(h / n**a)
        h += Q(1, n**b)
    increments = [sum(((-1)**k*comb(j,k)*coeff[k]
                       for k in range(j+1)), Q(0))
                  for j in range(m)]
    assert increments[0] == 0 and all(d < 0 for d in increments[1:])
    values = [Q(0)]
    for j,d in enumerate(increments):
        values.append(values[-1] + d/2**(j+1))
    return values


def check_fixed_pair_nonmonotonicity():
    """A concrete exact certificate that R_N need not decrease.

    Here (a,b)=(2,1). The scalar-domination theorem gives M=5/4,
    so E_M-(5/4)2**(-M) < g < E_M.
    """
    m = 96
    ev = euler_values(2, 1, m)
    lo, hi = ev[m]-Q(5,4*2**m), ev[m]
    intervals = {}
    for n in (1,2,4,8,16,32):
        intervals[n] = (2**n*(ev[n]-hi), 2**n*(ev[n]-lo))
    # This strict comparison is entirely rational.
    assert intervals[2][0] > intervals[1][1]
    return {
        "pair": [2,1], "reference_euler_terms": m,
        "scalar_domination_remainder_constant": "5/4",
        "proved_comparison": "R_2(2,1) > R_1(2,1)",
        "enclosures": {str(n): {"lo":str(lo), "hi":str(hi),
                                  "decimal_diagnostic":float((lo+hi)/2)}
                       for n,(lo,hi) in intervals.items()}}


def main():
    report = {"scope": "Finite exact checks supporting an all-parameter analytic proof"}
    report.update(check_scalar())
    report.update(check_geometric_tail())
    report["fixed_pair_scaled_errors"] = check_fixed_pair_nonmonotonicity()
    dest = Path(__file__).with_name("euler_domination_checks.json")
    dest.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k:v for k,v in report.items()
                      if k != "fixed_pair_scaled_errors"}, indent=2))
    print(report["fixed_pair_scaled_errors"]["proved_comparison"])
    for n,r in report["fixed_pair_scaled_errors"]["enclosures"].items():
        print(f"N={n}: {r['decimal_diagnostic']:.16g}")
    print(f"Exact rational certificate written to {dest.name}")


if __name__ == "__main__":
    main()
