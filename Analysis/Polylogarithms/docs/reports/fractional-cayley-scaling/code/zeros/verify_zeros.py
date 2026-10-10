#!/usr/bin/env python3
"""Replay finite evidence for the Bessel scaling / Lerch unfolding report.

Default: standard-library-only exact interval signs and logarithm bounds.
--diagnostics: additionally compare elementary and Lerch zeros with the
proved Bessel expansion using mpmath; these are numerical diagnostics.
The all-order theorems are proved in the accompanying article, not by a
finite numerical run.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from math import factorial
from pathlib import Path


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    products = [a * b for a in x for b in y]
    return min(products), max(products)


def log_interval(x, terms=100):
    """Positive x >= 1: exact atanh series with geometric remainder."""
    x = F(x)
    if x < 1:
        lo, hi = log_interval(1 / x, terms)
        return -hi, -lo
    u = (x - 1) / (x + 1)
    assert 0 <= u < 1
    partial = 2 * sum((u ** (2 * j + 1) / (2 * j + 1)
                       for j in range(terms)), F(0))
    tail = 2 * u ** (2 * terms + 1) / ((2 * terms + 1) * (1 - u * u))
    return partial, partial + tail


def rising_coefficients(k):
    """Exact ascending coefficients of (1+t)_k."""
    coefficients = [1]
    for j in range(1, k + 1):
        updated = [0] * (len(coefficients) + 1)
        for i, c in enumerate(coefficients):
            updated[i] += j * c
            updated[i + 1] += c
        coefficients = updated
    return coefficients


def elementary_coefficients(k):
    """Ascending coefficients of product_{j=1}^k(1+j t)."""
    coefficients = [1]
    for j in range(1, k + 1):
        coefficients.append(0)
        for i in range(j, 0, -1):
            coefficients[i] += j * coefficients[i - 1]
    return coefficients


def evaluate_interval(coefficients, x):
    result = (F(0), F(0))
    for c in reversed(coefficients):
        result = add(mul(result, x), (F(c), F(c)))
    return result


def normalized_f2(n, k, log2):
    """An interval for f_{n,k}(2)/n!, via its independent rising form."""
    rising = rising_coefficients(k)
    coefficients = [F(0)] * (n + 1)
    for i, c in enumerate(rising):
        if i <= n:
            degree = n - i
            coefficients[degree] = F((-1) ** degree * c,
                                     2 ** (k + 1) * factorial(degree))
    return evaluate_interval(coefficients, log2)


def outward_decimal_interval(interval, digits=60):
    scale = 10 ** digits
    lo = (interval[0].numerator * scale) // interval[0].denominator
    hi = -((-interval[1].numerator * scale) // interval[1].denominator)
    return {"lower_numerator": str(lo), "upper_numerator": str(hi),
            "denominator": "10^" + str(digits)}


def exact_evidence():
    log2 = log_interval(F(2))
    log74 = log_interval(F(7, 4))
    log4011 = log_interval(F(40, 11))
    assert log74[0] > F(11, 20)
    assert log4011[1] < F(13, 10)
    assert F(13, 20) - F(1, 2) - F(11, 48) < -F(1, 20)
    rows = []
    for k in range(1, 9):
        for r in range(1, 7):
            n = k + r
            interval = normalized_f2(n, k, log2)
            assert interval[0] > 0 or interval[1] < 0
            sign = 1 if interval[0] > 0 else -1
            count = k + (1 if r % 2 else 2 if sign < 0 else 0)
            rows.append({"n": n, "k": k, "r": r,
                         "f_over_n_factorial_sign": sign,
                         "f_over_n_factorial": outward_decimal_interval(interval),
                         "small_positive_rho_zero_count": count})
    return {"status": "48 exact rational interval signs passed",
            "interpretation": "Finite illustrations of the proved all-pair theorem.",
            "logarithm_terms": 100,
            "log2": outward_decimal_interval(log2),
            "log7_over4": outward_decimal_interval(log74),
            "log40_over11": outward_decimal_interval(log4011),
            "tail_constant_inequalities": "11/20 < log(7/4); log(40/11) < 13/10; -19/240 < -1/20",
            "rows": rows}


def diagnostic_evidence():
    import mpmath as mp
    mp.mp.dps = 250
    rows = []
    elementary = {k: elementary_coefficients(k) for k in (40, 80, 160)}

    def elementary_profile(z, r, k):
        e = elementary[k]
        return mp.fsum(mp.mpf(e[j]) / mp.mpf(k) ** (2 * j)
                       * (-z) ** (r + j) / mp.factorial(r + j)
                       for j in range(max(0, -r), k + 1))

    for r in (-3, -1, 0, 1, 3):
        for m in (1, 2):
            lam = mp.besseljzero(abs(r), m) ** 2 / 2
            for k in (40, 80, 160):
                approx = (lam - (2 * r + 5) * lam / (3 * k)
                          + lam * (4 * r * r + 15 * r + lam + 20) / (9 * k * k))
                root = mp.findroot(lambda z: elementary_profile(z, r, k),
                                   (approx * mp.mpf("0.995"), approx * mp.mpf("1.005")))
                rows.append({"r": r, "m": m, "k": k,
                             "lambda": mp.nstr(lam, 35),
                             "z_zero": mp.nstr(root, 35),
                             "k_cubed_times_z_error": mp.nstr(k ** 3 * (root - approx), 20)})

    deformation = []
    r = 0
    for k, cutoff in ((40, 256), (80, 96), (160, 48)):
        e = elementary[k]
        coefficients = [mp.mpf(e[j]) * (-1) ** j / mp.factorial(j)
                        for j in range(k + 1)]
        lam = mp.besseljzero(0, 1) ** 2 / 2
        z0 = mp.findroot(lambda z: elementary_profile(z, 0, k),
                        (lam * mp.mpf("0.9"), lam))

        def full_profile(z, rho):
            a = mp.exp(z / k ** 2)
            tail = mp.fsum(rho ** m * mp.polyval(list(reversed(coefficients)), mp.log(a + m))
                          / (a + m) ** (k + 1) for m in range(1, cutoff))
            return elementary_profile(z, 0, k) + a ** (k + 1) * tail

        for rho in (mp.mpf("0.5"), mp.mpf(1)):
            z = mp.findroot(lambda z: full_profile(z, rho),
                            (z0 - mp.mpf("1e-8"), z0 + mp.mpf("1e-8")))
            a, a0 = mp.exp(z / k ** 2), mp.exp(z0 / k ** 2)
            b = a + cutoff
            b0 = mp.mpf(7) / 4
            # Exact theorem's scalar bound evaluated numerically here. This
            # diagnostic number is not represented as an interval certificate.
            tail_bound = (mp.exp(7 - mp.mpf(k) / 20) * a ** (k + 1)
                          * (b0 / b) ** (mp.mpf(k) / 2)
                          * (1 / b + mp.mpf(2) / k))
            deformation.append({"r": 0, "m": 1, "k": k,
                                "rho": mp.nstr(rho), "spectral_cutoff": cutoff,
                                "a_zero": mp.nstr(a, 55),
                                "a_minus_elementary": mp.nstr(a - a0, 30),
                                "omitted_profile_tail_bound_numerical": mp.nstr(tail_bound, 12)})
    return {"status": "mpmath numerical diagnostics completed",
            "precision_decimal_digits": mp.mp.dps,
            "interpretation": "Diagnostics only; finite data do not prove the asymptotic theorem.",
            "elementary_root_rows": rows, "lerch_deformation_rows": deformation}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--diagnostics", action="store_true")
    parser.add_argument("--output", type=Path, default=Path(__file__).parent / "evidence")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    exact = exact_evidence()
    (args.output / "exact-signs.json").write_text(json.dumps(exact, indent=2) + "\n")
    print(exact["status"])
    if args.diagnostics:
        diagnostics = diagnostic_evidence()
        (args.output / "bessel-diagnostics.json").write_text(json.dumps(diagnostics, indent=2) + "\n")
        print(diagnostics["status"])
        print("30 elementary root rows; 6 Lerch deformation rows.")


if __name__ == "__main__":
    main()
