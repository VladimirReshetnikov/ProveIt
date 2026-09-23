#!/usr/bin/env python3
"""Exact finite checks for the accompanying surcomplex Gamma/zeta article.

These tests do not prove the general support, analytic, transfer, or RH claims.
Run: python code/verify.py --output /tmp/gamma-zeta-checks.json
The output path is mandatory so a rerun never silently overwrites shipped evidence.
"""
from __future__ import annotations

import argparse
import json
import platform
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checks: list[dict[str, Any]] = []

    def check(name: str, condition: bool) -> None:
        passed = bool(condition)
        checks.append({"name": name, "passed": passed})
        if not passed:
            raise AssertionError(f"Failed exact check: {name}")

    v, s, u, tau, eta = sp.symbols("v s u tau eta")
    A = sp.symbols("A", positive=True)

    # L_J(A+1)-L_J(A)-log(A), written in v=1/A.
    for J in range(1, 9):
        defect = (1 / v + sp.Rational(1, 2)) * sp.log(1 + v) - 1
        for k in range(1, J + 1):
            bk = sp.bernoulli(2*k) / (2*k*(2*k-1))
            defect += bk * v**(2*k-1) * ((1+v)**(1-2*k) - 1)
        truncated = sp.series(defect, v, 0, 2*J+2).removeO().expand()
        check(f"stirling_shift_J{J}_through_degree_{2*J+1}", truncated == 0)

    for k in range(1, 13):
        rising_derivative = sp.diff(sp.rf(s, 2*k-1), s).subs(s, 0)
        check(f"rising_factorial_derivative_k{k}",
              sp.simplify(rising_derivative - sp.factorial(2*k-2)) == 0)
        coefficient = sp.bernoulli(2*k) * rising_derivative / sp.factorial(2*k)
        expected = sp.bernoulli(2*k) / (2*k*(2*k-1))
        check(f"lerch_stirling_coefficient_k{k}", sp.simplify(coefficient-expected) == 0)

    base = A**(1-s)/(s-1) + sp.Rational(1, 2)*A**(-s)
    expected_base = (A-sp.Rational(1, 2))*sp.log(A)-A
    check("hurwitz_derivative_elementary_terms",
          sp.simplify(sp.diff(base, s).subs(s, 0)-expected_base) == 0)

    for m in range(13):
        z = -A**(m+1)/sp.Integer(m+1) + A**m/sp.Integer(2)
        for k in range(1, m+3):
            z += sp.bernoulli(2*k)*sp.rf(-m, 2*k-1)*A**(m+1-2*k)/sp.factorial(2*k)
        expected = -sp.bernoulli(m+1, A)/sp.Integer(m+1)
        check(f"hurwitz_negative_integer_m{m}", sp.simplify(z-expected) == 0)
        check(f"hurwitz_shift_m{m}", sp.simplify(z.subs(A,A+1)-z+A**m) == 0)

    # Finite arithmetic-function algebra: rational coefficients throughout.
    limit = 128
    def convolution(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
        result = [Fraction(0) for _ in range(limit+1)]
        for d in range(1, limit+1):
            if a[d]:
                for e in range(1, limit//d+1):
                    if b[e]:
                        result[d*e] += a[d]*b[e]
        return result

    ones = [Fraction(0)] + [Fraction(1) for _ in range(limit)]
    mu = [Fraction(0)] + [Fraction(int(sp.mobius(n))) for n in range(1, limit+1)]
    inverse = convolution(ones, mu)
    for n in range(1, limit+1):
        check(f"mobius_inverse_n{n}", inverse[n] == (1 if n == 1 else 0))

    w = ones.copy()
    w[1] = Fraction(0)
    power = w.copy()
    log_coeffs = [Fraction(0) for _ in range(limit+1)]
    for k in range(1, limit.bit_length()):
        factor = Fraction((-1)**(k+1), k)
        for n in range(1, limit+1):
            log_coeffs[n] += factor * power[n]
        power = convolution(power, w)
    for n in range(1, limit+1):
        factors = sp.factorint(n)
        expected = Fraction(1, next(iter(factors.values()))) if len(factors) == 1 else Fraction(0)
        check(f"log_euler_coefficient_n{n}", log_coeffs[n] == expected)

    a, b, h0, h1 = sp.symbols("a b h0 h1", nonzero=True)
    branch = -h0/a*eta + (h0*h1/a**2 - b*h0**2/a**3)*eta**2
    residual = a*branch + b*branch**2 + eta*(h0+h1*branch)
    check("simple_root_motion_second_order",
          sp.series(residual, eta, 0, 3).removeO().expand() == 0)

    quadratic_roots = [(1, sp.I), (1, -sp.I), (-1, sp.Integer(1)), (-1, sp.Integer(-1))]
    for j, (sign, root) in enumerate(quadratic_roots):
        check(f"quadratic_splitting_leading_root_{j}", sp.simplify(root**2+sign) == 0)
    cubic_roots = [-1, (1+sp.sqrt(3)*sp.I)/2, (1-sp.sqrt(3)*sp.I)/2]
    for j, root in enumerate(cubic_roots):
        check(f"cubic_splitting_leading_root_{j}", sp.simplify(root**3+1) == 0)

    for m in range(13):
        heat = sum((-tau)**j/sp.factorial(j)*sp.factorial(m)/sp.factorial(m-2*j)
                   *u**(m-2*j) for j in range(m//2+1))
        check(f"polynomial_backward_heat_degree_{m}",
              sp.simplify(sp.diff(heat, tau)+sp.diff(heat, u, 2)) == 0)
        check(f"polynomial_heat_initial_value_degree_{m}",
              sp.simplify(heat.subs(tau, 0)-u**m) == 0)
    check("negative_time_quadratic_nonreal_root", sp.simplify((sp.I*sp.sqrt(2))**2+2) == 0)

    result = {
        "article": "Gamma, Zeta, and the Riemann Hypothesis over Surcomplex Numbers",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "arithmetic": "Exact symbolic and rational arithmetic; no floating-point zero verification",
        "checks_total": len(checks),
        "checks_passed": sum(item["passed"] for item in checks),
        "formal_proof_assistant_checked": False,
        "limitations": [
            "Finite tests do not prove general Hahn summability or analytic implicit-function theory.",
            "No ultraproduct, surreal class theorem, or analytic-number-theory input is machine verified.",
            "No proof of RH, simplicity of all zeta zeros, or novelty claim is supplied by this script."
        ],
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"{result['checks_passed']}/{result['checks_total']} exact finite checks passed.")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
