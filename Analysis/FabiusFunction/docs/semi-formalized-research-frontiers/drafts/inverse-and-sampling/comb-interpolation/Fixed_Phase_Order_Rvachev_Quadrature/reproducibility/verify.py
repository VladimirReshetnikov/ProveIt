#!/usr/bin/env python3
"""Independent checks for the accompanying Rvachev quadrature manuscript.

The Fraction checks are exact finite arithmetic.  The mpmath checks are
floating-point diagnostics, NOT interval certificates or formal proofs.
Run: python reproducibility/verify.py [--exact-only | --numeric-only]
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(maxsize=None)
def dn(n: int) -> Q:
    if n == 0:
        return Q(1)
    return sum((comb(n + 1, k) * dn(k) for k in range(n)), Q(0)) / (
        (n + 1) * (2**n - 1)
    )


@lru_cache(maxsize=None)
def fabius(x: Q) -> Q:
    """Bounded Fabius function at an exact dyadic argument in [0,1]."""
    if not Q(0) <= x <= Q(1):
        raise ValueError("The argument must lie in [0,1].")
    den = x.denominator
    if den & (den - 1):
        raise ValueError("The exact evaluator accepts only dyadic rationals.")
    if x == 0:
        return Q(0)
    if x == 1:
        return Q(1)
    if x.numerator == 1:
        n = den.bit_length() - 1
        return dn(n) / (factorial(n) * 2**(n * (n - 1) // 2))
    n = 1
    while Q(1, 2**n) > x:
        n += 1
    y = x - Q(1, 2**n)
    return -fabius(y) + sum(
        (Q(2**(k*(k+1)//2), factorial(k)) *
         fabius(Q(1, 2**(n-k))) * y**k for k in range(n + 1)), Q(0)
    )


@lru_cache(maxsize=None)
def up(x: Q) -> Q:
    return fabius(1 - abs(x)) if abs(x) < 1 else Q(0)


@lru_cache(maxsize=None)
def moment(n: int) -> Q:
    if n == 0:
        return Q(1)
    if n % 2:
        return Q(0)
    return sum((Q(comb(n, k), n-k+1) * moment(k)
                for k in range(0, n, 2)), Q(0)) / (2**n-1)


@lru_cache(maxsize=None)
def quadrature(M: int, theta: Q, degree: int) -> Q:
    theta %= 1
    return sum((Q(k+theta, M)**degree * up(Q(k+theta, M))
                for k in range(-M-1, M+1)), Q(0)) / M


def defect(M: int, theta: Q, degree: int) -> Q:
    return quadrature(M, theta, degree) - moment(degree)


def selected(r: int) -> tuple[Q, Q]:
    return (Q(0), Q(1, 2)) if r % 2 else (Q(1, 4), Q(3, 4))


def exact_checks() -> dict:
    count = 0
    def check(test: bool) -> None:
        nonlocal count
        assert test
        count += 1
    check(fabius(Q(1, 2)) == Q(1, 2))
    check(fabius(Q(1, 4)) == Q(5, 72))
    check(moment(2) == Q(1, 9))
    for j in range(257):
        x = Q(j, 256)
        check(fabius(x) + fabius(1-x) == 1)
    rows = []
    for d in range(7):
        M, r = 2**d, d+1
        phases = selected(r)
        for j in range(16):
            theta = Q(j, 16)
            for degree in range(r):
                check(defect(M, theta, degree) == 0)
            check((defect(M, theta, r) == 0) == (theta in phases))
        errs = [defect(M, theta, r+1) for theta in phases]
        for theta, err in zip(phases, errs):
            check(defect(M, theta, r) == 0)
            check(err != 0)
        rows.append({"d": d, "M": M, "r": r,
                     "phases": list(map(str, phases)),
                     "next_defects": list(map(str, errs))})
    expected = [Q(-1, 9), Q(17, 1536), Q(97, 345600),
                Q(-9919, 4529848320)]
    for d, val in enumerate(expected):
        check(defect(2**d, selected(d+1)[0], d+2) == val)
    # Refinement is tested independently as an exact finite-sum identity.
    for M in [1, 2, 4]:
        for L in [2, 4]:
            for theta in [Q(0), Q(1, 8), Q(1, 4)]:
                for degree in range(7):
                    avg = sum((quadrature(M, theta+Q(j, L), degree)
                               for j in range(L)), Q(0))/L
                    check(avg == quadrature(L*M, L*theta, degree))
    return {"status": "PASS", "checks": count,
            "arithmetic": "fractions.Fraction (exact)", "dyadic_rows": rows}


def numerical_checks() -> dict:
    try:
        import mpmath as mp
    except ImportError as exc:
        raise SystemExit("Install mpmath, or use --exact-only.") from exc
    mp.mp.dps = 60
    count = 0
    def check(test: bool) -> None:
        nonlocal count
        assert test
        count += 1
    def conv(x: Q):
        return mp.mpf(x.numerator)/x.denominator
    @lru_cache(maxsize=None)
    def hd(odd_twice_t: int):
        t = mp.mpf(odd_twice_t)/2
        h, ell = mp.mpf(1), mp.mpf(0)
        for j in range(112):
            c = mp.pi/2**j
            z = c*t
            if abs(z) < mp.mpf('1e-12'):
                sinc = 1-z*z/6+z**4/120-z**6/5040
                dlog = -c*(z/3+z**3/45+2*z**5/945)
            else:
                sinc = mp.sin(z)/z
                dlog = c/mp.tan(z)-1/t
            h *= sinc
            ell += dlog
        return h, h*ell
    def tau(p: int, theta):
        return mp.cos(2*mp.pi*theta+p*mp.pi/2)
    def S(s: int):
        return (1-mp.mpf(2)**(-s))*mp.zeta(s)-1
    def params(m: int):
        A, hp = hd(m)
        beta = -(mp.mpf(m)/2)*hp/A
        P = mp.sinc(mp.pi*m/2)*mp.sinc(mp.pi*m/4)
        T = abs(A/P)
        D = mp.pi*m/4*(1+1/T)+mp.mpf(2)/3
        return A, beta, D
    def coeff(m: int, n: int):
        A, _ = hd(m)
        h, hp = hd(m*n)
        return h/A, mp.mpf(m)/2*hp/A
    odds = list(range(1, 202, 2))
    coefficient_rows = []
    for m in [1, 3, 5, 7, 9, 11, 13, 15, 17, 31]:
        A, beta, D = params(m)
        for n in range(3, 64, 2):
            a, b = coeff(m, n)
            check(abs(a) <= 1/mp.mpf(n)**2 + mp.mpf('1e-50'))
            check(abs(a) <= (1+mp.sqrt(2))/mp.mpf(n)**3 + mp.mpf('1e-50'))
            check(abs(b) <= D/mp.mpf(n)**2 + mp.mpf('1e-50'))
        cutoff = max(2, int(mp.ceil(2*abs(beta)+2)),
                     2+int(mp.ceil(mp.log(1+D, 3))))
        passed = []
        for r in range(1, 21):
            R = r*S(r+3) + D*S(r+2)
            if r % 2:
                R += 2**(-(r+1))*(1+S(r+3))
            if abs(r+beta) > R:
                passed.append(r)
        coefficient_rows.append({"m": m, "A": mp.nstr(A, 18),
                                 "beta": mp.nstr(beta, 18),
                                 "D": mp.nstr(D, 18),
                                 "conservative_cutoff_r": cutoff,
                                 "elementary_cutoff_r":
                                     2*max(2, 1+(m-1).bit_length())*(m+1)+4,
                                 "criterion_passes_r_1_to_20": passed})
    A, beta, D = params(1)
    check(beta > 1)
    check(D < mp.mpf(5)/2)
    ab = {n: coeff(1, n) for n in odds}
    next_rows = []
    max_error = mp.mpf(0)
    max_relative_deviation = mp.mpf(0)
    for d in range(7):
        M, r = 2**d, d+1
        p = r+1
        K = 2*mp.factorial(p)*A/(2*mp.pi*M)**p
        for theta_q in selected(r):
            theta = conv(theta_q)
            odd = mp.fsum((r*a/n**(r+1)-b/n**r)*tau(p, n*theta)
                         for n, (a, b) in ab.items())
            even = mp.fsum(a*tau(p, 2*n*theta)/n**p
                          for n, (a, _) in ab.items())/2**p
            value = conv(defect(M, theta_q, p))/K
            error = abs(value-(odd-even))
            max_error = max(max_error, error)
            # An absolute analytic tail envelope beyond n=201.
            def tail(s):
                return mp.mpf(201)**(-s)+mp.mpf(201)**(1-s)/(2*(s-1))
            envelope = r*tail(r+3)+D*tail(r+2)+2**(-p)*tail(p+2)
            check(error < envelope+mp.mpf('1e-45'))
            ratio = value/((r+beta)*tau(p, theta))
            check(mp.mpf(3)/4 < ratio < mp.mpf(5)/4)
            max_relative_deviation = max(max_relative_deviation, abs(ratio-1))
            next_rows.append({"d": d, "theta": str(theta_q),
                              "normalized_exact_defect": mp.nstr(value, 22),
                              "relative_to_leading_term": mp.nstr(ratio, 22),
                              "series_error": mp.nstr(error, 8)})
    return {"status": "PASS", "checks": count,
            "warning": "Numerical diagnostics, not interval-certified proofs.",
            "decimal_precision": mp.mp.dps, "product_factors": 112,
            "odd_series_cutoff": 201,
            "max_normalized_series_discrepancy": mp.nstr(max_error, 18),
            "max_dyadic_relative_deviation": mp.nstr(max_relative_deviation, 18),
            "parameter_rows": coefficient_rows, "next_defect_rows": next_rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--exact-only", action="store_true")
    group.add_argument("--numeric-only", action="store_true")
    args = parser.parse_args()
    out = ROOT / "validation"
    out.mkdir(parents=True, exist_ok=True)
    if not args.numeric_only:
        result = exact_checks()
        (out / "exact_results.json").write_text(json.dumps(result, indent=2)+"\n")
        print(f"Exact checks: PASS ({result['checks']})")
        for row in result["dyadic_rows"]:
            print(row)
    if not args.exact_only:
        result = numerical_checks()
        (out / "numerical_results.json").write_text(json.dumps(result, indent=2)+"\n")
        print(f"Numerical checks: PASS ({result['checks']})")
        print("Maximum normalized series discrepancy:",
              result["max_normalized_series_discrepancy"])
        print("Maximum dyadic leading-term relative deviation:",
              result["max_dyadic_relative_deviation"])


if __name__ == "__main__":
    main()
