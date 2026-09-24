#!/usr/bin/env python3
"""Exact finite checks for Differential Equations over Surreal and Surcomplex Numbers.

This is not an implementation of No or a machine verification of its theorems.
SymPy variables represent formal finite algebraic identities.  The derivation
on real-power monomials is modelled by delta = -t**2*d/dt; on expressions in x
it is ordinary differentiation, as appropriate for finite expressions in omega.

Run from any directory: python /path/to/code/verify_examples.py
The deterministic report is written to ../data/verification.json.
"""
from __future__ import annotations

import json
import platform
import sys
from pathlib import Path
from typing import Any

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

x, z = sp.symbols("x z")
t = sp.Symbol("t", positive=True)
u = sp.Symbol("u", real=True)
u_prime = sp.Symbol("u_prime", real=True)
U = sp.Symbol("U", nonzero=True)
I = sp.I
CHECKS: list[dict[str, Any]] = []


def assert_zero(name: str, expression: sp.Expr) -> None:
    """Require exact symbolic zero, not a numerical tolerance or heuristic test."""
    value = sp.simplify(sp.expand(expression))
    passed = value == sp.S.Zero
    CHECKS.append({"name": name, "passed": bool(passed)})
    if not passed:
        raise AssertionError(f"{name}: exact residual is {value!s}")


def delta(expression: sp.Expr) -> sp.Expr:
    return sp.expand(-t**2 * sp.diff(expression, t))


def apply_polynomial_operator(poly: sp.Poly, expression: sp.Expr) -> sp.Expr:
    return sp.expand(sum(coef * sp.diff(expression, x, power[0])
                         for power, coef in poly.terms()))


def main() -> None:
    # Rational powers: all coefficients are exact, and t is positive so the
    # ordinary symbolic power identities used in these finite checks are valid.
    exponents = [sp.Rational(-5, 2), sp.Rational(-1), sp.Rational(-1, 3),
                 sp.Rational(0), sp.Rational(1, 4), sp.Rational(1),
                 sp.Rational(4, 3), sp.Rational(2), sp.Rational(7, 2)]
    for r in exponents:
        assert_zero(f"monomial_derivative_r={r}", delta(t**r) + r*t**(r+1))
        if r != 1:
            primitive = t**(r-1)/(1-r)
            assert_zero(f"monomial_primitive_r={r}", delta(primitive)-t**r)
    # The missing t term needs -log(t), equal to log(omega).
    assert_zero("logarithmic_primitive", delta(-sp.log(t))-t)

    # Finite product rules on sparse expressions, including complex constants.
    polys = [1+t, t**-2+3*t**2, 1+I*t**3, t**sp.Rational(1, 2)-t**2]
    for j, f in enumerate(polys):
        for k, g in enumerate(polys):
            assert_zero(f"product_rule_{j}_{k}", delta(f*g)-delta(f)*g-f*delta(g))

    # Finite Neumann/resolvent truncations. Residual must equal the first
    # omitted derivative, with the indicated alternating sign.
    f = t + (1+I)*t**2 + 2*t**sp.Rational(3, 2)
    for lam in (sp.Integer(1), sp.Integer(2), I, 1+I):
        for n_terms in range(1, 7):
            deriv = f
            partial = sp.S.Zero
            for n in range(n_terms):
                partial += (-1)**n * lam**(-n-1) * deriv
                deriv = delta(deriv)
            expected = (-1)**(n_terms-1)*lam**(-n_terms)*deriv
            assert_zero(f"resolvent_lambda={lam}_N={n_terms}",
                        delta(partial)+lam*partial-f-expected)

    for n_terms in range(1, 17):
        partial = sum(sp.factorial(n)*t**(n+1) for n in range(n_terms))
        assert_zero(f"factorial_residual_N={n_terms}",
                    delta(partial)+partial-t+sp.factorial(n_terms)*t**(n_terms+1))

    # Riccati coefficients, recurrence, and exact formal truncation residual.
    coeffs: dict[int, sp.Expr] = {1: sp.Integer(1)}
    for n in range(2, 11):
        coeffs[n] = sp.cancel(sum(coeffs[j]*coeffs[n-j] for j in range(1, n))/(2*n-1))
    expected_coeffs = {1: sp.Integer(1), 2: sp.Rational(1, 3),
                       3: sp.Rational(2, 15), 4: sp.Rational(17, 315),
                       5: sp.Rational(62, 2835)}
    for n, expected in expected_coeffs.items():
        assert_zero(f"Riccati_displayed_coefficient_{n}", coeffs[n]-expected)
    for n in range(2, 11):
        assert_zero(f"Riccati_recurrence_{n}",
                    (2*n-1)*coeffs[n]-sum(coeffs[j]*coeffs[n-j] for j in range(1, n)))
    partial = sp.expand(sum(coeffs[n]*z**(2*n-1)*t**n for n in coeffs))
    residual = sp.Poly(sp.diff(partial, z)-partial**2-t, t)
    for n in range(0, 11):
        assert_zero(f"Riccati_residual_t^{n}", residual.nth(n))

    # Constant-coefficient kernel examples: these verify displayed finite
    # expressions, not the completeness classification of solution spaces.
    X = sp.Symbol("X")
    P = sp.Poly((X-1)**2*(X**2+1), X)
    for n in range(2):
        assert_zero(f"constant_coefficient_example_basis_{n}",
                    apply_polynomial_operator(P, x**n*sp.exp(x)))
    for lam in (sp.Integer(-2), sp.Integer(0), sp.Rational(1, 2), sp.Integer(3)):
        for m in range(1, 5):
            Q = sp.Poly((X-lam)**m, X)
            for n in range(m):
                assert_zero(f"real_primary_kernel_lambda={lam}_m={m}_n={n}",
                            apply_polynomial_operator(Q, x**n*sp.exp(lam*x)))
    assert_zero("forced_oscillator_polynomial", sp.diff(x**3-6*x, x, 2)+x**3-6*x-x**3)
    assert_zero("first_order_inhomogeneous_constant", -I*I-1)

    # A finite-phase identity in the rational Cayley coordinate.
    phase = (1+I*u)/(1-I*u)
    assert_zero("Cayley_phase_logarithmic_derivative",
                sp.diff(phase, u)*u_prime/phase-2*I*u_prime/(1+u**2))
    assert_zero("Cayley_phase_unit_norm", phase*sp.conjugate(phase)-1)

    # The oscillator lives in a separately adjoined rational differential
    # extension, with delta(U)=i*U, not inside a claimed surreal representation.
    S = (U-U**-1)/(2*I)
    C = (U+U**-1)/2
    dU = lambda value: sp.cancel(I*U*sp.diff(value, U))
    assert_zero("extension_sine_derivative", dU(S)-C)
    assert_zero("extension_cosine_derivative", dU(C)+S)
    assert_zero("extension_circle_identity", S**2+C**2-1)
    assert_zero("extension_second_derivative", dU(dU(S))+S)

    # Total-vs-coordinate chain rule example F(z,t)=t*z.
    assert_zero("total_derivative_of_t_times_omega", t - (1/t)*t**2)

    report = {
        "scope": "Exact finite symbolic regression checks; not formal proofs of surreal theorems",
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "checks": len(CHECKS),
        "passed": sum(item["passed"] for item in CHECKS),
        "failed": sum(not item["passed"] for item in CHECKS),
        "riccati_coefficients": {str(n): str(coeffs[n]) for n in sorted(coeffs)},
        "results": CHECKS,
    }
    output = Path(__file__).resolve().parent.parent / "data" / "verification.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {report['passed']}/{report['checks']} exact checks; "
          f"Python {report['python']}, SymPy {report['sympy']}.")
    print(f"Report: {output}")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
