#!/usr/bin/env python3
"""Independent checks for the Mellin/polylogarithm continuation.

Exact checks are rational identities. Decimal quadratures are diagnostics,
not interval certificates and not substitutes for the analytic proofs.
Run: python verify_mellin_polylog.py --output mellin_checks.json
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import mpmath as mp
import sympy as sp


X, T = sp.symbols("X T")


def qpoly(m: int, k: int):
    return sp.Poly(sp.rf(X, k) * sp.rf(1 - X, m - k - 1)
                   / sp.factorial(m - 1), X)


def exact_z(s: int):
    return sp.Integer(1) if s == 0 else s * sp.zeta(s + 1)


def negative_polylog_numerators(limit: int):
    # Li_{-q}(-x)=p_q(x)/(1+x)^{q+1}, obtained by x d/dx.
    polynomials = [sp.Poly(-X, X)]
    for q in range(limit):
        p = polynomials[-1].as_expr()
        next_p = X * ((1 + X) * sp.diff(p, X) - (q + 1) * p)
        polynomials.append(sp.Poly(sp.expand(next_p), X))
    return polynomials


def exact_checks(max_m=14, max_q=12):
    counts = {"factored_operator_recurrence": 0,
              "hurwitz_shift_annihilation": 0,
              "integer_resonance_annihilation": 0,
              "nonpositive_order_beta_integrals": 0}
    polys = negative_polylog_numerators(max_q)
    for m in range(1, max_m + 1):
        pmt = sp.rf(1 - T - X, m - 1)
        for n in range(m - 1):
            assert sp.expand(pmt.subs(X, n + 1 - T)) == 0
            counts["hurwitz_shift_annihilation"] += 1
        for k in range(m):
            q = qpoly(m, k)
            if k:
                assert q == qpoly(m - 1, k - 1) - qpoly(m, k - 1)
                counts["factored_operator_recurrence"] += 1
            for n in range(1, m - k):
                assert sp.rf(1 - k - n, m - 1) == 0
                counts["integer_resonance_annihilation"] += 1
            for v in range(max_q + 1):
                # Direct integration of a rational negative-order polylog.
                lhs = sp.Integer(0)
                for (j,), coefficient in polys[v].terms():
                    a, b = k + j, m + v + 1 - k - j
                    assert a > 0 and b > 0
                    beta = sp.factorial(a - 1) * sp.factorial(b - 1)
                    beta /= sp.factorial(a + b - 1)
                    lhs += coefficient * beta
                rhs = -sum(coefficient * exact_z(-v - j)
                           for (j,), coefficient in q.terms())
                assert sp.cancel(lhs - rhs) == 0, (m, k, v, lhs, rhs)
                counts["nonpositive_order_beta_integrals"] += 1
    return counts


def li_negative_integer_order(n: int, x):
    """Li_n(-x), n positive integer, x>0, with elementary inversion."""
    if x <= 1:
        return mp.polylog(n, -x)
    y = mp.log(x)
    polynomial = -(2 * mp.pi * 1j) ** n / mp.factorial(n)
    polynomial *= mp.bernpoly(n, mp.mpf("0.5") + y / (2 * mp.pi * 1j))
    value = -(-1) ** n * mp.polylog(n, -1 / x) + polynomial
    return mp.re(value)


def positive_integer_quad(m: int, k: int, n: int, scale=1):
    # Logistic coordinate; finite subdivisions resolve the origin and tails.
    def integrand(y):
        x = mp.exp(y)
        return mp.exp(k * y) / (1 + x) ** m * li_negative_integer_order(n, scale * x)
    return mp.quad(integrand, [-mp.inf, -4, 0, 4, mp.inf])


def numeric_z(s):
    return mp.mpf(1) if s == 0 else s * mp.zeta(s + 1)


def numeric_integer_checks():
    mp.mp.dps = 40
    rows = []
    for m, k, s in [(1, 0, 1), (1, 0, 3), (2, 0, 2), (2, 1, 1),
                    (3, 1, 4), (3, 2, 2), (4, 2, 3), (6, 3, 4)]:
        lhs = positive_integer_quad(m, k, s)
        rhs = -sum(mp.mpf(int(c.p)) / int(c.q) * numeric_z(s - j)
                   for (j,), c in qpoly(m, k).terms())
        error = abs(lhs - rhs)
        assert error < mp.mpf("1e-32"), (m, k, s, error)
        rows.append({"m": m, "k": k, "s": s,
                     "value": mp.nstr(lhs, 36),
                     "absolute_error": mp.nstr(error, 5)})
    L = mp.log(2)
    special = [(1, 0, 2, mp.mpf("0.5"),
                -mp.mpf(7) * mp.zeta(3) / 4 + mp.pi**2 * L / 12 + L**3 / 6),
               (1, 0, 2, mp.mpf(2),
                -mp.mpf(7) * mp.zeta(3) / 4 - mp.pi**2 * L / 4),
               (3, 1, 3, mp.mpf(2),
                mp.pi**2 * (1 - L) / 8 - mp.mpf(7) * mp.zeta(3) / 8)]
    for m, k, s, scale, rhs in special:
        lhs = positive_integer_quad(m, k, s, scale)
        error = abs(lhs - rhs)
        assert error < mp.mpf("1e-32"), (m, k, s, scale, error)
        rows.append({"m": m, "k": k, "s": s, "scale": str(scale),
                     "value": mp.nstr(lhs, 36),
                     "absolute_error": mp.nstr(error, 5)})
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(Path(__file__).with_name("mellin_checks.json")))
    args = parser.parse_args()
    report = {"exact_checks": exact_checks(),
              "quadrature_precision_digits": 40,
              "quadratures_are_certified_intervals": False,
              "integer_and_scaled_quadratures": numeric_integer_checks()}
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
