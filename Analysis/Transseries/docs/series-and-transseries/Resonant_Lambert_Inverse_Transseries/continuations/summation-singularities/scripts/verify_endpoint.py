#!/usr/bin/env python3
"""Exact formal checks and numerical diagnostics for endpoint ramification.

The symbolic reference is fixed-point series reversion of Y_q(v); it does
not use the coefficient formula being checked. The numeric root reference
uses the defining polylogarithm, with a real positive root in v=t^(1/q).
These checks supplement the proof, and are not interval certificates.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy as sp


def truncate(expr, variable, order):
    return sp.series(expr, variable, 0, order + 1).removeO().expand()


def exact_checks():
    y, v = sp.symbols("y v")
    c = sp.symbols("c", nonzero=True)
    a, b = sp.symbols("a b")
    rows = []
    for q, order in [(2, 6), (3, 9)]:
        inverse = y / c
        for _ in range(order):
            inverse = truncate((y - a * inverse**q - b * inverse**(2*q)) / c,
                               y, order)
        residual = truncate(c*inverse + a*inverse**q + b*inverse**(2*q) - y,
                            y, order)
        assert residual == 0
        exponent = truncate(inverse**q, y, order)
        direct = truncate(sum((-exponent)**k / sp.factorial(k)
                              for k in range(order // q + 1)), y, order)
        for n in range(1, order+1):
            if n < q:
                lagrange = sp.Integer(0)
            else:
                degree = n-q
                expression = (sp.exp(-v**q) *
                              (c + a*v**(q-1) + b*v**(2*q-1))**(-n))
                lagrange = (-sp.Rational(q, n) *
                            truncate(expression, v, degree).coeff(v, degree))
            reference = direct.coeff(y, n)
            assert sp.simplify(reference - lagrange) == 0
            support_member = any(n-q-j*(q-1) >= 0 and
                                 (n-q-j*(q-1)) % q == 0
                                 for j in range(max(0, n-q)+1))
            if not support_member:
                assert reference == 0
            rows.append({"q": q, "degree": n,
                         "coefficient": str(sp.factor(reference)),
                         "fixed_point_matches_lagrange": True})
    return rows


def numeric_checks():
    mp.mp.dps = 80
    roots = []
    for q in (2, 3):
        s = 1 + mp.mpf(1)/q
        rho = mp.zeta(s)
        c = -mp.gamma(-mp.mpf(1)/q)
        a = mp.zeta(mp.mpf(1)/q)
        for y in (mp.mpf("0.01"), mp.mpf("0.001")):
            residual = lambda v: rho-mp.polylog(s, mp.exp(-v**q))-y
            guess = y/c
            root = mp.findroot(residual, (guess*mp.mpf("0.9"),
                                         guess*mp.mpf("1.1")),
                               solver="secant", tol=mp.mpf("1e-65"))
            assert root > 0
            reference = mp.exp(-root**q)
            if q == 2:
                approximation = (1-y**2/c**2 + 2*a*y**3/c**4 +
                                 (1/(2*c**4)-5*a*a/c**6)*y**4)
                next_degree = 5
            else:
                approximation = (1-y**3/c**3 + 3*a*y**5/c**6 +
                                 y**6/(2*c**6)-12*a*a*y**7/c**9)
                next_degree = 8
            error = abs(approximation-reference)
            assert error < y**next_degree
            roots.append({"q": q, "y": str(y),
                          "reference": mp.nstr(reference, 55),
                          "polynomial": mp.nstr(approximation, 55),
                          "absolute_error": mp.nstr(error, 20),
                          "error_over_next_power": mp.nstr(error/y**next_degree, 20),
                          "root_forward_residual": mp.nstr(abs(residual(root)), 10)})
    cut = []
    u = mp.mpf("1e-6")
    for s in (mp.mpf("1.25"), mp.mpf("1.49"),
              mp.mpf("1.5"), mp.mpf("1.51")):
        upper = mp.polylog(s, mp.exp(u)+mp.j*mp.mpf("1e-100"))
        expansion = (mp.zeta(s) + mp.gamma(1-s)*mp.exp(-mp.j*mp.pi*(s-1))*u**(s-1)
                     + mp.fsum(mp.zeta(s-k)*u**k/mp.factorial(k)
                               for k in range(1, 32)))
        gap = abs(upper)-mp.zeta(s)
        assert abs(upper-expansion) < mp.mpf("1e-65")
        assert (gap < 0) == (s < mp.mpf("1.5"))
        cut.append({"s": str(s), "u": str(u),
                    "modulus_gap": mp.nstr(gap, 40),
                    "independent_expansion_error": mp.nstr(abs(upper-expansion), 10)})
    return {"root_comparisons": roots, "cut_diagnostics": cut,
            "critical_squared_modulus_coefficient": mp.nstr(
                4*mp.pi+2*mp.zeta(mp.mpf("1.5"))*mp.zeta(mp.mpf("0.5")), 45)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"results"/"endpoint_checks.json")
    args = parser.parse_args()
    record = {"description": "Exact formal reversion and non-certified numerical diagnostics",
              "sympy_version": sp.__version__, "mpmath_version": mp.__version__,
              "exact_coefficients": exact_checks(), "numerical": numeric_checks()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(record['exact_coefficients'])} exact coefficients; "
          f"four root comparisons; four upper-bank diagnostics. {args.output}")


if __name__ == "__main__":
    main()
