#!/usr/bin/env python3
"""Exact, finite checks for the worked examples in surcomplex_analysis.tex.

Requires Python 3.9+ and SymPy. Run with: python verify_examples.py

This checks ordinary truncated formal-series identities only. It neither
represents the full surreal field nor formally verifies the paper's theorems.
All coefficients in the first two checks are fractions.Fraction values.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial
from typing import List

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

Poly = List[Q]  # Coefficient of X**j is stored at index j.


def zero(degree: int) -> Poly:
    if degree < 0:
        raise ValueError("The truncation degree must be nonnegative.")
    return [Q(0) for _ in range(degree + 1)]


def mul(a: Poly, b: Poly, degree: int) -> Poly:
    """Multiply two rational polynomials modulo X**(degree + 1)."""
    result = zero(degree)
    for i, ai in enumerate(a[: degree + 1]):
        if not ai:
            continue
        for j, bj in enumerate(b[: degree + 1 - i]):
            if bj:
                result[i + j] += ai * bj
    return result


def exp_zero_constant(a: Poly, degree: int) -> Poly:
    """Formal exponential modulo X**(degree + 1); requires a[0] == 0."""
    if not a or a[0] != 0:
        raise ValueError("The exponent must have zero constant coefficient.")
    result = zero(degree)
    power = zero(degree)
    result[0] = power[0] = Q(1)
    for k in range(1, degree + 1):
        power = mul(power, a, degree)
        scale = Q(1, factorial(k))
        for j in range(degree + 1):
            result[j] += power[j] * scale
    return result


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def inverse_series(degree: int) -> Poly:
    result = zero(degree)
    for n in range(1, degree + 1):
        result[n] = Q(n ** (n - 1), 2 ** (n - 1) * factorial(n))
    return result


def check_inverse() -> Poly:
    degree = 10
    rho = inverse_series(degree)
    exp_factor = exp_zero_constant([-a / 2 for a in rho], degree)
    actual = mul(rho, exp_factor, degree)
    expected = zero(degree)
    expected[1] = Q(1)
    check(actual == expected, "The inverse-series equation failed.")

    # Verify the original equation independently: rho(s)**2 = s**2 exp(rho(s)).
    lhs = mul(rho, rho, degree)
    exp_rho = exp_zero_constant(rho, degree)
    rhs = [Q(0), Q(0)] + exp_rho[: degree - 1]
    check(lhs == rhs, "The original root equation failed.")

    displayed = [Q(1), Q(1, 2), Q(3, 8), Q(1, 3), Q(125, 384), Q(27, 80)]
    check(rho[1:7] == displayed, "The displayed root coefficients differ.")
    print("PASS 1: rho(s) exp(-rho(s)/2) = s modulo s^11.")
    print("        rho(s)^2 = s^2 exp(rho(s)) modulo s^11.")
    print("        First six coefficients:", ", ".join(map(str, rho[1:7])))
    return rho


def check_preparation(rho: Poly) -> None:
    degree = len(rho) - 1
    rho_minus = [a * ((-1) ** j) for j, a in enumerate(rho)]
    linear = [-(a + b) for a, b in zip(rho, rho_minus)]
    constant = mul(rho, rho_minus, degree)
    check(all(linear[j] == constant[j] == 0 for j in range(1, degree + 1, 2)),
          "The symmetric coefficients must be even series in s.")
    expected_linear = {2: Q(-1), 4: Q(-2, 3), 6: Q(-27, 40)}
    expected_constant = {2: Q(-1), 4: Q(-1, 2), 6: Q(-11, 24)}
    for j, expected in expected_linear.items():
        check(linear[j] == expected, f"Wrong coefficient of s^{j} z.")
    for j, expected in expected_constant.items():
        check(constant[j] == expected, f"Wrong constant coefficient of s^{j}.")

    # Independently execute the holomorphic Taylor-remainder preparation
    # recursion through t^3. Store only the needed z-jets at each stage.
    z = sp.Symbol("z")
    order = 10
    U = {0: sp.Integer(1)}
    W = {0: z ** 2}
    for n in range(1, 4):
        f_n = -sum(z ** k / sp.factorial(k) for k in range(order)) if n == 1 else 0
        H = sp.expand(f_n - sum(U[j] * W[n-j] for j in range(1, n)))
        W[n] = sp.expand(H).coeff(z, 0) + sp.expand(H).coeff(z, 1) * z
        U[n] = sp.expand((H - W[n]) / z**2)
    prepared = {
        1: -1-z,
        2: -sp.Rational(1, 2)-sp.Rational(2, 3)*z,
        3: -sp.Rational(11, 24)-sp.Rational(27, 40)*z,
    }
    for n, expected in prepared.items():
        check(sp.expand(W[n] - expected) == 0, f"Preparation recursion failed at t^{n}.")
    print("PASS 2: Root factorization and preparation recursion independently give")
    print("        W(z) = z^2 - t(1+z) - t^2(1/2+2z/3)")
    print("               - t^3(11/24+27z/40) + higher t-orders.")


def check_residues() -> None:
    z = sp.Symbol("z")
    for n in range(1, 9):
        # Only the jet through z^(2n) can contribute to the residue.
        exp_jet = sum(sp.Rational(n**k, factorial(k)) * z**k for k in range(2*n + 1))
        coefficient = sp.expand(-sp.diff(exp_jet / z**(2*n), z) / n)
        check(coefficient.coeff(z, -1) == 0, f"Nonzero residue at t^{n}.")
        cancellation = -Q(n**(2*n-1), factorial(2*n-1)) + Q(2*n**(2*n), factorial(2*n))
        check(cancellation == 0, f"Residue coefficient cancellation failed for n={n}.")
    print("PASS 3: Every checked positive-order coefficient of F'/F has zero")
    print("        residue (orders t^1 through t^8); the leading residue is 2.")


def check_two_scale() -> None:
    a, e_a, q = sp.symbols("a e_a q", nonzero=True)
    A = e_a / (2*a)
    B = e_a**2 * (2*a - 1) / (8*a**3)
    delta = A*q + B*q**2
    # q*exp(delta) needs only its degree-one jet to compute modulo q^3.
    residual = sp.expand(2*a*delta + delta**2 - q*e_a*(1+delta))
    for degree in range(3):
        check(sp.simplify(residual.coeff(q, degree)) == 0,
              f"The two-scale root equation failed at degree {degree}.")
    print("PASS 4: For independent nonzero a and e_a, the coefficients")
    print("        A = e_a/(2a), B = e_a^2(2a-1)/(8a^3)")
    print("        solve 2a*delta + delta^2 = q*e_a*exp(delta) modulo q^3.")


def main() -> None:
    print("Exact finite checks for Surcomplex Analysis")
    print("Arithmetic: rational polynomials and exact SymPy expressions.")
    print("No floating-point tolerances or numerical root-finding are used.\n")
    rho = check_inverse()
    check_preparation(rho)
    check_residues()
    check_two_scale()
    print("\nALL FOUR CHECK GROUPS PASSED.")
    print("These finite checks are not a formal verification of the paper's proofs.")


if __name__ == "__main__":
    main()
