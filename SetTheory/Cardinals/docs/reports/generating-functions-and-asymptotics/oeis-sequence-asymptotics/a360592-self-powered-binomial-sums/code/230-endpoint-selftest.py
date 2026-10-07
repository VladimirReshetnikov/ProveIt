#!/usr/bin/env python3
"""Independent exact checks for Report230; no third-party dependency by default.

Includes finite-difference reconstruction from integer samples, independent
formal-product counts, displayed coefficient checks, central-moment identities,
and validation checks in both ordinary Python and python -O.
Optional --numerical adds small mpmath diagnostics.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import subprocess
import sys

import endpoint as ep

_checks = 0


def check(condition, description):
    global _checks
    if not condition:
        raise AssertionError(description)
    _checks += 1


def expect_error(error, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except error:
        check(True, "validation")
    else:
        raise AssertionError(f"{function.__name__}{args!r} failed to raise {error.__name__}")


def evaluate(poly, x):
    return sum(a*x**d for d, a in poly.items())


def sample_exp(p, r, order):
    """Direct scalar Taylor coefficients of the simplified product G_r(z).

    No Faulhaber, polynomial interpolation, or Touchard conversion is used here.
    """
    q = p+1
    ell = [F(0)]
    for j in range(1, order+1):
        ell.append((-1)**j*F(p, q)*(F((p*r)**(j+1), j+1)+F(r*(p*r)**j, j))
                   +F((-1)**(j+1), j)*sum((p*r-q*h)**j for h in range(r)))
    h = [F(1)]
    for j in range(1, order+1):
        h.append(sum(F(k, j)*ell[k]*h[j-k] for k in range(1, j+1)))
    return ell, h


def independent_expectations(p, order):
    samples = [sample_exp(p, r, order)[1] for r in range(2*order+4)]
    result = []
    for j in range(order+1):
        values = [h[j] for h in samples]
        differences = []
        while values:
            differences.append(values[0])
            values = [b-a for a, b in zip(values, values[1:])]
        check(all(v == 0 for v in differences[2*j+1:]), "independent H degree")
        result.append({d: v/factorial(d) for d, v in enumerate(differences) if v})
        for r in (2*order+4, 3*order+7):
            check(sum(v*comb(r, d) for d, v in enumerate(differences) if d <= r)
                  == sample_exp(p, r, j)[1][j], "unused interpolation sample")
    return result


def product_counts(p, limit):
    # Truncate sum_m x^m*(1+m^p*x^p)^m, multiplying factors directly.
    answer = [0]*(limit+1)
    for m in range(limit+1):
        poly = [1]+[0]*limit
        for _ in range(m):
            for d in range(limit, p-1, -1):
                poly[d] += m**p*poly[d-p]
        for d in range(limit-m+1):
            answer[m+d] += poly[d]
    return answer


def guard_checks():
    for fn in (ep.defect_polynomials, ep.coefficient_arrays, ep.fractional_coefficients, ep.marked_coefficients):
        for bad in (True, 2.0, "2", F(2)):
            expect_error(TypeError, fn, bad, 1)
            expect_error(TypeError, fn, 2, bad)
        for bad in (-1, ep.MAX_P+1):
            expect_error(ValueError, fn, bad, 1)
        expect_error(ValueError, fn, 2, -1)
        expect_error(ValueError, fn, 2, 10**9)
    for fn in (ep.coefficient_arrays, ep.fractional_coefficients, ep.marked_coefficients):
        expect_error(ValueError, fn, 1, 2)
    expect_error(ValueError, ep.fractional_coefficients, 2, ep.MAX_ORDER+1)
    for fn, limit in ((ep.critical_coefficients, ep.MAX_CRITICAL_ORDER), (ep.touchard, 2*ep.MAX_ORDER)):
        for bad in (True, 2.0, "2"):
            expect_error(TypeError, fn, bad)
        expect_error(ValueError, fn, -1)
        expect_error(ValueError, fn, limit+1)
    for bad in (True, 2.0, "2"):
        expect_error(TypeError, ep.exact_count, bad, 2)
        expect_error(TypeError, ep.exact_count, 2, bad)
        expect_error(TypeError, ep.marked_coefficients, 2, 2, bad)
    for bad in (-1, ep.MAX_EXACT_N+1):
        expect_error(ValueError, ep.exact_count, 2, bad)
    expect_error(ValueError, ep.exact_count, 0, 1)
    expect_error(ValueError, ep.exact_count, ep.MAX_P+1, 1)
    expect_error(ValueError, ep.marked_coefficients, 2, 2, 0)
    expect_error(ValueError, ep.marked_coefficients, 2, 2, ep.MAX_CUMULANT+1)
    # Importing diagnostics itself does not require mpmath. These calls must
    # reject invalid/resource-exceeding arguments before numerical computation.
    import diagnostics as dg
    expect_error(ValueError, dg.finite_sum_diagnostic, 2, 0)
    expect_error(ValueError, dg.finite_sum_diagnostic, 2, ep.MAX_EXACT_N+1)
    expect_error(TypeError, dg.finite_sum_diagnostic, 2, True)
    expect_error(ValueError, dg.finite_sum_diagnostic, 2, 10, dps=29)
    expect_error(ValueError, dg.finite_sum_diagnostic, 2, 10, h_order=ep.MAX_ORDER+1)
    expect_error(ValueError, dg.marked_diagnostic, 1, 10**6)
    expect_error(ValueError, dg.marked_diagnostic, 2, 10**13)
    expect_error(TypeError, dg.marked_diagnostic, 2, 1000.0)
    expect_error(ValueError, dg.newton_diagnostic, 2, 10**13)
    expect_error(ValueError, dg.newton_diagnostic, 2, ep.MAX_EXACT_N+1, exact_target=True)
    expect_error(TypeError, dg.newton_diagnostic, 2, 1000, exact_target="yes")
    expect_error(ValueError, dg.newton_diagnostic, 2, 1000, steps=13)


def exact_checks():
    for p in range(1, 7):
        values = [ep.exact_count(p, n) for n in range(36)]
        check(product_counts(p, 35) == values, "independent formal product count")
        check(values[:p+1] == [1]*(p+1), "initial plateau")
        check(values[p+1] == 2, "first nontrivial count")
        check(all(values[n+1] > values[n] for n in range(p, 35)), "strict monotonicity")
        for j, dpoly in enumerate(ep.defect_polynomials(p, 6)):
            check(not dpoly or max(dpoly) <= j+1, "D degree")
            for r in (0, 1, 2, 7, 19):
                check(evaluate(dpoly, r) == sample_exp(p, r, 6)[0][j], "independent D sample")
    for p in (2, 3, 4, 7):
        D, H, U = ep.coefficient_arrays(p, 6)
        check(U == independent_expectations(p, 6), "independent factorial-moment U")
        for j in range(7):
            check(max(H[j], default=0) <= 2*j, "H degree")
            for r in (0, 3, 15):
                check(evaluate(H[j], r) == sample_exp(p, r, 6)[1][j], "independent H sample")
        A = (F(p*p)+F(1, p+1))/2
        b = A-F(p+1, 2)
        cc = F(p**3, 3)-F(1, 6*(p+1))
        dd, ee = F(p*p-1, 4), F((p+1)**2, 12)
        L, theta2 = ep.marked_coefficients(p, 3)
        check(L[1] == {1: -b, 2: -A}, "marked first logarithm")
        expectedL2 = {1: cc-dd-ee+b*b/2, 2: 3*cc-dd+A*A+2*A*b, 3: cc+2*A*A}
        check(L[2] == expectedL2, "independent factorial-covariance L2")
        check(theta2[2] == {d: a*d*d for d, a in expectedL2.items()}, "second cumulant operator")
    check(ep.touchard(0) == {0: F(1)}, "T0")
    check(ep.touchard(4) == {1: F(1), 2: F(7), 3: F(6), 4: F(1)}, "T4")
    C2 = ep.fractional_coefficients(2, 4)
    check(C2 == [{0: F(1)}, {2: -F(13, 6)}, {1: -F(2, 3), 4: F(169, 72)},
                 {3: F(121, 9), 6: -F(2197, 1296)},
                 {2: F(134, 9), 5: -F(2977, 108), 8: F(28561, 31104)}], "p=2 displayed C0..C4")
    check(ep.fractional_coefficients(3, 6) == [
        {0: F(1)}, {}, {2: -F(37, 8)}, {1: -F(21, 8)}, {4: F(1369, 128)},
        {3: F(12265, 192)}, {2: F(9471, 128), 6: -F(50653, 3072)}], "p=3 displayed C0..C6")
    for p in range(3, 10):
        check(all(not v for v in ep.fractional_coefficients(p, p-2)[1:]), "structural missing powers")
    critical = [{0: F(1)}, {1: F(1, 4), 3: F(11, 8)},
                {2: F(31, 32), 4: -F(319, 96), 6: F(121, 128)},
                {1: -F(5, 96), 3: -F(739, 128), 5: F(46517, 3840), 7: -F(7381, 1536), 9: F(1331, 3072)},
                {2: -F(227, 128), 4: F(61923, 2048), 6: -F(771061, 15360), 8: F(4140367, 184320), 10: -F(41261, 12288), 12: F(14641, 98304)}]
    check(ep.critical_coefficients(4) == critical, "critical displayed C0..C4")
    for k in range(5):
        check(ep.critical_coefficients(k) == critical[:k+1], "critical order coherence")
    # Central moment substitution checked independently by binomial recentering
    # of ordinary moments, at several rational Poisson parameters.
    for d in range(12):
        for c in (F(1, 3), F(2), F(7, 2)):
            centered = sum(comb(d, k)*(-c)**(d-k)*evaluate(ep.touchard(k), c) for k in range(d+1))
            associated = sum(ep._associated(d, k)*c**k for k in range(d//2+1))
            check(centered == associated, "independent centered Poisson moment")


def numerical_checks():
    import mpmath as mp
    import diagnostics as dg
    for p in (1, 2, 3, 4):
        for n in range(50, 51+p):
            row = dg.finite_sum_diagnostic(p, n, 4, 4, 70)
            check(mp.mpf(row["identity_relative_discrepancy"]) < mp.mpf("1e-60"), "complete transformed identity, every residue")
    for p in (1, 2, 3):
        row = dg.newton_diagnostic(p, 10**6, 4, 3, 80)
        errs = [mp.mpf(x) for x in row["index_errors"]]
        check(abs(errs[-1]) < mp.mpf("1e-25"), "finite Newton accuracy")
        check(all(a >= b-mp.mpf("1e-60") for a, b in zip(errs, errs[1:])), "decreasing Newton iterates")
    row = dg.marked_diagnostic(2, 10**6, 80)
    check(mp.mpf(row["tv_original_absolute_truncation_bound"]) < mp.mpf("1e-50"), "marked tail bound")
    check(mp.mpf(row["tv_tilted_window"]) < mp.mpf(row["tv_original_window"]), "tilted improvement")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--guards-only", action="store_true")
    parser.add_argument("--numerical", action="store_true", help="also run small optional mpmath checks")
    args = parser.parse_args()
    guard_checks()
    if not args.guards_only:
        exact_checks()
        if args.numerical:
            numerical_checks()
        result = subprocess.run([sys.executable, "-B", "-O", str(Path(__file__).resolve()), "--guards-only"],
                                capture_output=True, text=True, check=False)
        check(result.returncode == 0, "python -O validation: "+result.stdout+result.stderr)
        print(result.stdout.strip())
    print(f"PASS: {_checks} checks ({'optimized' if not __debug__ else 'ordinary'} Python)")


if __name__ == "__main__":
    main()
