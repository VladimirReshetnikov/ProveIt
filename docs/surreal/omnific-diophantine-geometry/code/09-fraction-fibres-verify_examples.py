#!/usr/bin/env python3
"""Exact finite checks for the accompanying omnific-fractions article.

This is NOT a surreal arithmetic implementation or a proof checker.  In
particular it does not test proper-class quantifiers, support separation,
non-generation of ideals, or historical novelty.

Requires Python 3.9+ and SymPy 1.14.0.  Run from any working directory;
verification_report.json is written next to this script.  A failed check
raises AssertionError and exits nonzero.
"""
from __future__ import annotations

import json
import platform
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import sympy as sp


CHECKS: list[dict[str, Any]] = []


def check(name: str, condition: bool, detail: str = "") -> None:
    """Record an assertion, rejecting unknown symbolic truth values."""
    if condition is not True:
        raise AssertionError(f"FAILED: {name}: {detail}")
    CHECKS.append({"name": name, "passed": True, "detail": detail})


def zero(name: str, expression: sp.Expr) -> None:
    """Prove a displayed finite rational identity by exact simplification."""
    reduced = sp.simplify(sp.cancel(expression))
    check(name, reduced == 0, f"residual = {reduced}")


def matrix_zero(name: str, matrix: sp.Matrix) -> None:
    reduced = matrix.applyfunc(lambda e: sp.simplify(sp.cancel(e)))
    check(name, reduced == sp.zeros(*matrix.shape), f"shape = {matrix.shape}")


def transvection(x: sp.Expr, b: sp.Expr) -> sp.Matrix:
    return sp.Matrix([[1 + b*x, -b*x*x], [b, 1 - b*x]])


def main() -> None:
    T, x, b, c, z, r = sp.symbols("T x b c z r")
    I = sp.eye(2)
    N = sp.Matrix([[x, -x*x], [1, -x]])
    G = transvection(x, b)
    matrix_zero("nilpotence N_x^2 = 0", N*N)
    zero("transvection determinant", G.det() - 1)
    matrix_zero("transvection unipotent form", G - I - b*N)
    matrix_zero("transvection composition", G*transvection(x, c) - transvection(x, b+c))
    matrix_zero("transvection inverse", G*transvection(x, -b) - I)
    action = ((1+b*x)*z-b*x*x)/(b*z+1-b*x)
    zero("fractional-linear action formula", action - x - (z-x)/(1+b*(z-x)))
    zero("fixed centre", action.subs(z, x)-x)
    zero("image of infinity", (1+b*x)/b - x - 1/b)
    zero("direct nearby Bezout certificate", (1-b*x)*(1+b*x)+(b*x*x)*b-1)
    zero("one-scale Bezout certificate", (1-r*T)*(1+r*T)+(r*r*T)*T-1)
    zero("opposite-type example difference", (r+1/T)-(r+1/(T+1))-1/(T*(T+1)))

    # Verify covariance's inverse scalar formula as a formal rational identity.
    a, d, k = sp.symbols("a d k")
    det = a*d-b*c
    y = (a*x+b)/(c*x+d)
    zero("denominator covariance inverse scalar", k*(a-c*y)/det-k/(c*x+d))
    zero("denominator covariance inverse numerator", k*(d*y-b)/det-x*k/(c*x+d))

    sqrt2 = sp.sqrt(2)
    examples = [
        ("ordinary rational", sp.Integer(2), sp.Integer(3), sp.Rational(2, 3), True),
        ("irrational real", sqrt2, sp.Integer(1), sqrt2, False),
        ("ordinary denominator at infinite value", sqrt2*T+sp.Rational(3,5), sp.Integer(1), sp.Rational(3,5), True),
        ("rational direction 3:7", 2*T+3, 5*T+7, sp.Rational(3,7), True),
        ("irrational coefficient rational direction", sqrt2*T+2, T+3, sp.Rational(2,3), True),
        ("irrational direction", T+sqrt2, T+1, sqrt2, False),
        ("quadratic irrational direction", T*T+1, T*T+sqrt2, 1/sqrt2, False),
        ("pole at zero", sqrt2*T+1, T, sp.oo, True),
        ("shifted pole example", sqrt2*T+sqrt2+1, T+1, sqrt2+1, False),
    ]
    sample_results: list[dict[str, Any]] = []
    for name, P, Q, expected, rational_direction in examples:
        P = sp.sympify(P)
        Q = sp.sympify(Q)
        U, V, gcd = sp.gcdex(P, Q, T, extension=sqrt2)
        zero(f"{name}: polynomial coprimality", gcd-1)
        zero(f"{name}: polynomial Bezout", U*P+V*Q-1)
        p, q = P.subs(T, 0), Q.subs(T, 0)
        check(f"{name}: nonzero constant vector", not (p == 0 and q == 0))
        if q == 0:
            sigma = sp.oo
            check(f"{name}: specialization at infinity", expected == sp.oo)
        else:
            sigma = sp.simplify(p/q)
            zero(f"{name}: specialization", sigma-expected)
        rational_actual = sigma == sp.oo or sigma.is_Rational is True
        check(f"{name}: direction type", rational_actual == rational_direction)
        data: dict[str, Any] = {"name": name, "P": str(P), "Q": str(Q), "specialization": str(sigma)}
        if rational_direction:
            if q == 0:
                lam = 1/p
                m, n = sp.Integer(1), sp.Integer(0)
            else:
                m, n = sigma.as_numer_denom()
                lam = n/q
            A, B = sp.expand(lam*P), sp.expand(lam*Q)
            u0, v0 = sp.cancel(U/lam), sp.cancel(V/lam)
            ui, vi, g_int = sp.gcdex(m, n)
            zero(f"{name}: primitive integer constant vector", g_int-1)
            alpha, beta = u0.subs(T,0), v0.subs(T,0)
            correction = sp.simplify((ui-alpha)/n if n != 0 else (beta-vi)/m)
            u1 = sp.simplify(u0+correction*B)
            v1 = sp.simplify(v0-correction*A)
            zero(f"{name}: lifted omnific Bezout", u1*A+v1*B-1)
            zero(f"{name}: first Bezout constant", u1.subs(T,0)-ui)
            zero(f"{name}: second Bezout constant", v1.subs(T,0)-vi)
            check(f"{name}: integer Bezout constants", ui.is_Integer is True and vi.is_Integer is True)
            data.update({"multiplier_lambda": str(lam), "numerator": str(A),
                         "denominator_generator": str(B), "Bezout_U": str(u1), "Bezout_V": str(v1)})
        else:
            data["denominator_ideal_formula"] = f"({Q}) * Pi (theorem, not computationally verified)"
        sample_results.append(data)

    # Verify the auxiliary local-density construction on a nontrivial example.
    f = (T*T+2)/(T*T*(T-1))
    L, M = 3, 4  # pole order at 0 is 2; H has degree -12 at infinity
    H = 1/(1+T**L)**M
    g = sp.cancel((1-H)*f+sqrt2*H)
    zero("local-density error identity", g-f-H*(sqrt2-f))
    zero("local-density specialization", sp.limit(g, T, 0)-sqrt2)
    num, den = sp.fraction(sp.cancel(g-f))
    error_degree = sp.degree(num,T)-sp.degree(den,T)
    check("local-density prescribed accuracy", bool(error_degree < -10), f"degree = {error_degree}")

    # Finite exact order examples check the estimate, not the full-class choice of b.
    centre = sp.Rational(7,3)
    eps = sp.Rational(1,100)
    B = sp.Integer(1000)
    points = [sp.Rational(-100), sp.Rational(0), centre,
              centre+sp.Rational(1,10), sp.Rational(100)]
    for j, point in enumerate(points):
        value = centre+(point-centre)/(1+B*(point-centre))
        check(f"finite focusing sample {j}", bool(abs(value-centre)<eps), f"exact image = {value}")
    check("finite focusing infinity", bool(1/B<eps))

    output = {
        "status": "all exact finite checks passed",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "assertion_count": len(CHECKS),
        "scope": "Finite symbolic identities and sample data only; not a theorem prover.",
        "not_verified": ["surreal normal-form theory", "proper-class or set-separation arguments",
                         "denominator-ideal classification for all inputs", "failure of set generation",
                         "full-class density or focusing", "Lean formalization", "historical novelty"],
        "checks": CHECKS,
        "one_scale_examples": sample_results,
    }
    destination = Path(__file__).resolve().with_name("verification_report.json")
    destination.write_text(json.dumps(output, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
    print(f"Passed {len(CHECKS)} exact finite assertions. Wrote {destination.name}.")
    print("These checks do not verify the surreal/proper-class theorems.")


if __name__ == "__main__":
    main()
