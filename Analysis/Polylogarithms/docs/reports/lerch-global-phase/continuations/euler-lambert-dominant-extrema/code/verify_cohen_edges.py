#!/usr/bin/env python3
"""Replay algebra and high-precision diagnostics for the Lambert edge theorem.

The theorem and its uniform remainder are proved analytically in
sections/07_cohen_extremes.tex. Numerical root calculations here are diagnostics,
not substitutes for that proof. Exact finite checks use Fraction. The
symbolic check uses SymPy and the optional numerical check uses mpmath.

Usage:
    python verify_cohen_edges.py --numeric --output cohen_edge_checks.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import platform


def stirling_rows(targets):
    row = [1]
    result = {}
    for n in range(1, max(targets) + 1):
        row = [0] + [(row[r - 1] if r else 0)
                     + (n - 1) * (row[r] if r < len(row) else 0)
                     for r in range(1, n + 1)]
        if n in targets:
            result[n] = row[:]
    return result


def operator_polynomial(n, k):
    """Apply the exact normalization in (cohen-operator)."""
    N = n + k - 1
    p = [Fraction(0)] * N + [Fraction(1)]
    for r in range(1, n):
        p = [p[i] + (i + 1) * p[i + 1] / r if i < N else p[i]
             for i in range(N + 1)]
    return [(-1) ** (n + i) * Fraction(k, n) * x
            for i, x in enumerate(p)]


def cohen_stirling_polynomial(n, k, row):
    """Cohen Prop 4.8, signed Stirling numbers converted to unsigned."""
    p = [Fraction(0)] * (n + k)
    pref = (-1) ** (n + k) * math.factorial(k) * math.comb(n + k - 1, n)
    for j in range(1, n + 1):
        signed_stirling = (-1) ** (j - 1) * row[n + 1 - j]
        p[k - 1 + j] = Fraction(pref * signed_stirling,
                                math.factorial(k - 1 + j))
    return p


def finite_exact_checks():
    rows = stirling_rows(set(range(1, 15)))
    for n in range(1, 15):
        for k in range(1, 6):
            assert operator_polynomial(n, k) == cohen_stirling_polynomial(n, k, rows[n])
    return {"status": "passed", "arithmetic": "exact rational",
            "operator_vs_Cohen_Stirling": {"n": [1, 14], "k": [1, 5]}}


def symbolic_checks():
    import sympy as s
    N, j, ell, c, s2, s3, kap = s.symbols("N j ell c s2 s3 kap")
    moments = []
    for r in range(6):
        moment = s.expand(sum((-1) ** (r - h) * s.binomial(r, h)
                              * s.prod(N - a for a in range(h)) / N ** h
                              for h in range(r + 1)))
        moments.append(moment)
    assert moments == [1, 0, -1 / N, 2 / N ** 2,
                        3 / N ** 2 - 6 / N ** 3,
                        -20 / N ** 3 + 24 / N ** 4]
    q1, q1p = j * (j + 1) / 2, j + s.Rational(1, 2)
    r2, r3, r4 = 2 * c, 3 * (c ** 2 - s2), 4 * (c ** 3 - 3 * c * s2 + 2 * s3)
    T10 = -j ** 2 * (r2 - 2 * ell) / 2
    T11 = -j ** 2 * (q1 * r2 + 2 * q1p - 2 * ell * q1) / 2
    T10p = -j * (r2 - 2 * ell) - j ** 2 * (r3 - 2 * ell * r2 + ell ** 2) / 2
    T20 = (j ** 3 * (r3 - 3 * ell * r2 + 3 * ell ** 2) / 3
           + j ** 4 * (r4 - 4 * ell * r3 + 6 * ell ** 2 * r2 - 4 * ell ** 3) / 8)
    alpha = s.expand(-T10)
    beta0 = s.expand(-(c * alpha ** 2 + q1 * alpha + T10p * alpha + T11 + T20))
    betakap = beta0 - kap * alpha
    C = s.simplify(alpha ** 2 / j ** 3 - (betakap + kap * alpha) / j ** 2)
    expected = j ** 2 * s3 - j * s2 - j - s.Rational(1, 2)
    assert s.simplify(C - expected) == 0
    return {"status": "passed", "sympy_version": s.__version__,
            "moments_M0_to_M5": [str(x) for x in moments],
            "alpha": str(alpha), "beta0": str(beta0),
            "C_j_after_exact_cancellation": str(C),
            "independence_of_kappa": bool(s.diff(C, kap) == 0),
            "independence_of_log_n": bool(s.diff(C, ell) == 0)}


def numerical_checks():
    import mpmath as mp
    mp.mp.dps = 100
    ns = [64, 128, 256, 512, 1024]
    rows = stirling_rows(set(ns))
    data = []
    fmt = lambda x: mp.nstr(x, 38)
    C0 = -mp.mpf(3) / 2 - mp.zeta(2) - mp.zeta(3)
    for n in ns:
        for k in [1, 2, 4]:
            N = n + k - 1
            denom = math.factorial(n - 1)
            fall = mp.mpf(1)
            coeff = []
            for r in range(n):
                if r:
                    fall *= mp.mpf(N - r + 1) / N
                coeff.append((-1) ** r * fall * mp.mpf(rows[n][r + 1]) / denom)
            q = lambda w: mp.polyval(list(reversed(coeff)), w)
            for j in [1, 2, 3]:
                H1 = mp.fsum(mp.mpf(1) / a for a in range(1, j))
                H2 = mp.fsum(mp.mpf(1) / a ** 2 for a in range(1, j))
                H3 = mp.fsum(mp.mpf(1) / a ** 3 for a in range(1, j))
                Cj = j ** 2 * (H3 - mp.zeta(3)) - j * (H2 + mp.zeta(2)) - j - mp.mpf(1) / 2
                lead = mp.mpf(N) / j + mp.log(n) + mp.euler - H1
                prediction = lead + Cj / n
                guess = mp.mpf(N) / prediction
                w = mp.findroot(q, (guess * mp.mpf("0.999"), guess * mp.mpf("1.001")),
                                tol=mp.mpf("1e-85"), verify=True)
                assert 0 < w < j and abs(w - guess) < mp.mpf("0.15")
                X = N / w
                item = {"n": n, "k": k, "j_decreasing_index": j,
                             "root_X": fmt(X), "reciprocal_root_w": fmt(w),
                             "n_times_root_minus_leading_terms": fmt(n * (X - lead)),
                             "predicted_C_j": fmt(Cj),
                             "prediction_error": fmt(X - prediction),
                             "n2_times_prediction_error": fmt(n ** 2 * (X - prediction)),
                             "absolute_polynomial_residual": fmt(abs(q(w)))}
                if j == 1:
                    C1 = ((k - 1) * (mp.zeta(2) + mp.zeta(3))
                          + mp.zeta(2) ** 2 - mp.zeta(2) * mp.zeta(3)
                          + 2 * mp.zeta(3) + 3 * mp.zeta(5) - mp.mpf(1) / 12)
                    item["predicted_Cohen_C1_k"] = fmt(C1)
                    item["n3_times_error_after_C1_n2"] = fmt(n ** 3 * (X - prediction - C1 / n ** 2))
                data.append(item)
    return {"status": "diagnostic computations completed", "precision_digits": mp.mp.dps,
            "mpmath_version": mp.__version__,
            "Cohen_C0_exact_expression": "-3/2-zeta(2)-zeta(3)",
            "Cohen_C0_decimal": fmt(C0),
            "caution": "Floating point diagnostics; the error bound and root ordering are proved in the article.",
            "rows": data}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--numeric", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {"python_version": platform.python_version(), "exact": finite_exact_checks(),
              "symbolic": symbolic_checks()}
    if args.numeric:
        result["numerical"] = numerical_checks()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "exact": result["exact"]["status"],
                      "symbolic": result["symbolic"]["status"],
                      "numeric_rows": len(result.get("numerical", {}).get("rows", []))}))


if __name__ == "__main__":
    main()
