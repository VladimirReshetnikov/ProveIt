#!/usr/bin/env python3
"""Replay finite algebraic certificates and numerical ladder diagnostics.

The proof is in ladder_proofs.tex.  Exact checks below certify the algebraic
argument substitutions and rational row operations, relative to the stated
classical functional equations.  Numerical residuals are diagnostics only.
Dependencies: Python 3, sympy, mpmath.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path

import mpmath as mp
import sympy as sp


def exact_checks() -> dict:
    r = sp.Symbol("r")
    polynomial = r**3 + r - 1
    checks = []

    def check(label, lhs, rhs):
        num, den = sp.fraction(sp.cancel(lhs - rhs))
        assert sp.rem(num, polynomial, r) == 0, label
        assert sp.rem(den, polynomial, r) != 0, label + " denominator"
        checks.append(label)

    factorizations = [
        (1 - r, r**3),
        (1 - r**2, r**3 * (1 + r)),
        (1 - r**3, r),
        (1 - r**4, r**2 * (1 + r)),
        (1 + r**3, r**2 * (1 + r) ** 2),
        (1 - r**6, r**3 * (1 + r) ** 2),
    ]
    for j, (lhs, rhs) in enumerate(factorizations, 1):
        check(f"factorization_{j}", lhs, rhs)

    def kummer_args(x, y):
        return [x, y, x * (1-y) / (x-1), y * (1-x) / (y-1),
                (1-x) / (1-y), x * (1-y) / (y * (1-x)), x*y,
                x/y, x * (1-y)**2 / (y * (1-x)**2)]

    expected = [
        [r, r**3, -r**-1, -r**5, r**2, r**-4, r**4, r**-2, r**-6],
        [-r, r**2, r**4, -r**-1, r**-3, -r**2, -r**3, -r**-1, -r**5],
    ]
    signs_and_powers = [
        [(1,1),(1,3),(-1,-1),(-1,5),(1,2),(1,-4),(1,4),(1,-2),(1,-6)],
        [(-1,1),(1,2),(1,4),(-1,-1),(1,-3),(-1,2),(-1,3),(-1,-1),(-1,5)],
    ]
    for j, ((x,y), expected_row) in enumerate(
            zip([(r,r**3),(-r,r**2)], expected), 1):
        for k, (actual, target) in enumerate(zip(kummer_args(x,y), expected_row), 1):
            check(f"kummer_{j}_argument_{k}", actual, target)

    def reduce_row(row):
        result = {}
        for coefficient, (sign, power) in zip([2]*6+[-1]*3, row):
            power = abs(power)
            if sign == 1:
                result[power] = result.get(power, F(0)) + coefficient
            else:
                result[power] = result.get(power, F(0)) - coefficient
                result[2*power] = result.get(2*power, F(0)) + F(coefficient, 4)
        return {k: v for k,v in result.items() if v}

    A = {1:F(1), 2:F(-1), 3:F(1), 4:F(1,4)}
    B, C = [reduce_row(row) for row in signs_and_powers]
    assert B == {2:F(3,2), 3:F(2), 4:F(1), 5:F(-2), 6:F(-1), 10:F(1,2)}
    assert C == {1:F(-3), 2:F(3,4), 3:F(3), 4:F(5,2), 5:F(1), 6:F(-1,4), 10:F(-1,4)}
    result = {k: 4*C.get(k,0)+2*B.get(k,0)-48*A.get(k,0)
              for k in set(A)|set(B)|set(C)}
    result = {k:v for k,v in result.items() if v}
    assert result == {1:-60,2:54,3:-32,6:-3}
    assert 4*2+2*2-48 == -36
    checks.append("cubic_P3_row_operation")

    s, t = r/(1+r), r**4/(1+r)
    pentagons = [
        (r,r,(s,s)),
        (r,r**3,(1-s,t)),
        (r**2,r**4,(s,t)),
        (r,r**2,(1-r**2,r**4)),
    ]
    for j,(x,y,(target1,target2)) in enumerate(pentagons,1):
        check(f"pentagon_{j}_argument_1", x*(1-y)/(1-x*y), target1)
        check(f"pentagon_{j}_argument_2", y*(1-x)/(1-x*y), target2)

    L, H = sp.symbols("L H")
    assert sp.expand(3*L*(3*L+2*H)-6*L*(3*L+H)+3*L**2+6*L**2) == 0
    assert sp.expand(-60*3*L+216*(3*L+H)-288*L-108*(3*L+2*H)) == -144*L
    checks.extend(["Rogers_log_tail_cancellation", "P3_log_tail_cancellation"])

    return {"passed": len(checks), "checks": checks,
            "P3_certificate": {"A":{str(k):str(v) for k,v in A.items()},
                               "B":{str(k):str(v) for k,v in B.items()},
                               "C":{str(k):str(v) for k,v in C.items()},
                               "combination":"4*C+2*B-48*A",
                               "result":{str(k):str(v) for k,v in result.items()}}}


def positive_root(a, b):
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(mp.mp.prec + 8):
        mid = (lo+hi)/2
        if mid == lo or mid == hi:
            break
        if mid**a + mid**b < 1:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2


def li3_series(z):
    if z == 1:
        return mp.zeta(3)
    term, total, n = z, mp.mpf(0), 1
    tolerance = mp.power(10, -mp.mp.dps+10)
    while True:
        total += term / n**3
        tail_bound = term*z / ((n+1)**3 * (1-z))
        if tail_bound < tolerance:
            return total
        term *= z
        n += 1


def numerical_checks(digits):
    with mp.workdps(digits):
        cases = [(1,1),(1,2),(1,3),(1,4),(1,5),(1,7),
                 (2,3),(2,5),(3,4),(4,9),(7,11)]
        residuals, series_errors = {}, []
        for a,b in cases:
            r = positive_root(a,b)
            L = mp.log(r)
            d = b-a
            args = [r**a,r**b,r**d,r**(2*d)]
            vals = [mp.polylog(3,z) for z in args]
            rhs = mp.zeta(3) + a*mp.pi**2*L/6 + a*a*(a-3*b)*L**3/6
            residuals[f"complementary_{a}_{b}"] = abs(vals[0]+vals[1]-vals[2]+vals[3]/4-rhs)
            for z,v in zip(args,vals):
                series_errors.append(abs(li3_series(z)-v))
        r = positive_root(1,3)
        L = mp.log(r)
        c = {1:-60,2:54,3:-32,6:-3}
        lhs = mp.fsum(v*mp.polylog(3,r**k) for k,v in c.items())
        residuals["cubic_raw"] = abs(lhs-(24*L**3-4*mp.pi**2*L-36*mp.zeta(3)))
        residuals["cubic_dilog"] = abs(mp.polylog(2,r**6)-6*mp.polylog(2,r**2)
                                            +2*mp.polylog(2,r)+4*mp.polylog(2,r**3))
        threshold = mp.power(10,-digits+12)
        assert max(residuals.values()) < threshold
        assert max(series_errors) < threshold
        return {"working_decimal_digits":digits,
                "residuals":{k:mp.nstr(v,12) for k,v in residuals.items()},
                "maximum_series_comparison_error":mp.nstr(max(series_errors),12),
                "threshold":mp.nstr(threshold,12),
                "note":"Numerical diagnostics, not an equality or interval certificate."}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--digits", type=int, nargs="+", default=[100,200])
    args = parser.parse_args()
    report = {"exact":exact_checks(),
              "numerical":[numerical_checks(d) for d in args.digits]}
    output = json.dumps(report,indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    print(output)


if __name__ == "__main__":
    main()
