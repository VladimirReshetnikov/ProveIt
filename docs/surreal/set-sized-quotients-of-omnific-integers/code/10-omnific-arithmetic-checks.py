#!/usr/bin/env python3
"""Exact finite regression checks for Set-Sized Shadows of Omnific Arithmetic.

Requires Python 3.10+ and SymPy. These checks are NOT a formal verification of
class-sized statements, arbitrary Hahn supports, or the main research claims.
They use deterministic exact arithmetic and terminate with a nonzero status
when a check fails.
"""
from __future__ import annotations

from collections import defaultdict
from math import comb, factorial, lcm
import platform
import sys
from typing import Callable

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install the required package with: python -m pip install sympy") from exc

X, T, Y, Z, W = sp.symbols("X T Y Z W")


def require(condition: bool, explanation: str) -> None:
    """Do not use assert: checks should also run under python -O."""
    if not condition:
        raise AssertionError(explanation)


def binomial_polynomial(x: sp.Expr, k: int) -> sp.Expr:
    if k < 0:
        raise ValueError("The binomial degree must be nonnegative.")
    return sp.Rational(1, factorial(k)) * sp.prod(x - j for j in range(k))


def integer_binomial(n: int, k: int) -> int:
    """The polynomial binomial coefficient, including negative n."""
    if k < 0:
        raise ValueError("The binomial degree must be nonnegative.")
    if n >= 0:
        return comb(n, k) if n >= k else 0
    return (-1) ** k * comb(k - n - 1, k)


def check_divided_differences() -> int:
    count = 0
    require(binomial_polynomial(X, 0) is sp.S.One, "B_0 must be an exact symbolic one.")
    for k in range(1, 11):
        left = binomial_polynomial(X + T, k) - binomial_polynomial(X, k)
        right = T * sum(
            binomial_polynomial(X, k - j)
            * binomial_polynomial(T - 1, j - 1) / j
            for j in range(1, k + 1)
        )
        require(sp.expand(left - right) == 0, f"Divided difference failed at k={k}")
        count += 1
    return count


def check_congruences() -> int:
    count = 0
    for k in range(11):
        multiplier = lcm(*range(1, k + 1)) if k else 1
        for a in range(-18, 19):
            for b in range(-18, 19):
                if a == b:
                    continue
                difference = multiplier * (integer_binomial(a, k) - integer_binomial(b, k))
                require(difference % (a - b) == 0,
                        f"Congruence failed: k={k}, a={a}, b={b}")
                count += 1
    require((integer_binomial(2, 2) - integer_binomial(0, 2)) % 2 == 1,
            "The B_2 obstruction was not detected.")
    return count + 1


def finite_difference_at_zero(poly: sp.Expr, variables: tuple[sp.Symbol, ...],
                              orders: tuple[int, ...]) -> sp.Expr:
    current = poly
    for variable, order in zip(variables, orders, strict=True):
        for _ in range(order):
            current = sp.expand(current.subs(variable, variable + 1) - current)
    return sp.expand(current.subs({variable: 0 for variable in variables}))


def check_newton() -> int:
    U, V = sp.symbols("U V")  # Formal placeholders, not an encoding of surreals.
    poly = X**5 / 120 - X**3 / 7 + U * (X**4 - 3*X) + V
    reconstructed = sum(
        finite_difference_at_zero(poly, (X,), (k,)) * binomial_polynomial(X, k)
        for k in range(6)
    )
    require(sp.expand(poly - reconstructed) == 0, "Univariate Newton reconstruction failed.")
    tensor = X**3 * Y**2 / 6 + U * X**2 * Y + V * (Y - X) + sp.Rational(5, 11)
    reconstructed_tensor = sum(
        finite_difference_at_zero(tensor, (X, Y), (k, ell))
        * binomial_polynomial(X, k) * binomial_polynomial(Y, ell)
        for k in range(4) for ell in range(3)
    )
    require(sp.expand(tensor - reconstructed_tensor) == 0,
            "Tensor Newton reconstruction failed.")
    require(sp.expand(binomial_polynomial(sp.I, 2)) == (-1 - sp.I) / 2,
            "Gaussian binomial counterexample failed.")
    return 3


def indicator_mod(n: int, a: int, p: int, k: int, e: int) -> int:
    """Evaluate the article's E^(p^(e-1)) modulo p^e exactly."""
    modulus = p**e
    value = 1
    for j in range(k):
        digit = (a // (p**j)) % p
        factor = 1 - pow((integer_binomial(n, p**j) - digit) % modulus, p - 1, modulus)
        value = (value * factor) % modulus
    return pow(value, p**(e - 1), modulus)


def check_padic_indicators() -> int:
    count = 0
    for p in (2, 3, 5):
        for k in range(1, 4):
            period = p**k
            # Full one-level grid of representatives, plus negative and larger inputs.
            samples = list(range(-period, 2*period + 1)) + [period**2 + 7, -period**2 - 9]
            for e in range(1, 4):
                for a in range(period):
                    for n in samples:
                        expected = int((n - a) % period == 0)
                        actual = indicator_mod(n, a, p, k, e)
                        require(actual == expected,
                                f"Indicator failed: p={p}, k={k}, e={e}, a={a}, n={n}")
                        count += 1
    # Explicit finite synthesis of a two-variable locally constant function.
    p, k, e = 3, 1, 2
    modulus = p**e
    values = {(a, b): (a*a + 2*a*b + 4*b + 1) % modulus
              for a in range(p) for b in range(p)}
    for n in range(-5, 8):
        for m in range(-5, 8):
            actual = sum(c * indicator_mod(n, a, p, k, e) * indicator_mod(m, b, p, k, e)
                         for (a, b), c in values.items()) % modulus
            require(actual == values[n % p, m % p], "Bivariate residue synthesis failed.")
            count += 1
    return count


def check_geometric_telescoping() -> int:
    count = 0
    for N in range(41):
        product: dict[tuple[int, int], int] = defaultdict(int)
        for n in range(N + 1):
            exponent = (1, -n - 2)
            require(exponent > (0, 0), "Lexicographic positivity failed.")
            product[(exponent[0], exponent[1] + 2)] += 1
            product[(exponent[0], exponent[1] + 1)] -= 1
        reduced = {a: c for a, c in product.items() if c}
        require(reduced == {(1, 0): 1, (1, -N - 1): -1},
                f"Geometric telescoping failed at N={N}.")
        count += 1
    return count


def check_rational_differences() -> int:
    count = 0
    for m in range(1, 5):
        rational = 3 / X**m + 5 / X**(m + 1)
        for k in range(6):
            numerator, denominator = sp.fraction(sp.cancel(rational))
            numerator_poly = sp.Poly(numerator, X)
            denominator_poly = sp.Poly(denominator, X)
            expected_coefficient = (-1)**k * 3 * sp.rf(m, k)
            require(numerator_poly.degree() - denominator_poly.degree() == -m-k,
                    f"Rational difference degree failed: m={m}, k={k}.")
            require(sp.cancel(numerator_poly.LC() / denominator_poly.LC()) == expected_coefficient,
                    f"Rational difference leading coefficient failed: m={m}, k={k}.")
            count += 1
            rational = sp.cancel(rational.subs(X, X + 1) - rational)
    return count


def check_scaled_polynomial_difference() -> int:
    count = 0
    for d in range(2, 9):
        coeffs = sp.symbols(f"a0:{d+1}")
        poly = sum(coeffs[j] * X**j for j in range(d+1))
        quotient = sum(coeffs[j] * sum((T*Z)**(j-1-ell) * (T*W)**ell
                                     for ell in range(j))
                       for j in range(1, d+1))
        require(sp.expand(poly.subs(X, T*Z) - poly.subs(X, T*W)
                          - T*(Z-W)*quotient) == 0,
                f"Polynomial divided difference failed at d={d}.")
        normalized = sum(Z**(d-1-ell) * W**ell for ell in range(d))
        for j in range(1, d):
            normalized += coeffs[j] / (coeffs[d] * T**(d-j)) * sum(
                Z**(j-1-ell) * W**ell for ell in range(j)
            )
        require(sp.cancel(quotient / (coeffs[d] * T**(d-1)) - normalized) == 0,
                f"Normalized divided difference failed at d={d}.")
        require(sp.expand(sum(Z**(d-1-ell) * W**ell for ell in range(d)).subs(W, Z)
                          - d*Z**(d-1)) == 0,
                f"Reduced diagonal failed at d={d}.")
        count += 3
    return count


def main() -> int:
    print("Exact finite checks: Set-Sized Shadows of Omnific Arithmetic")
    print(f"Python {platform.python_version()}; SymPy {sp.__version__}")
    checks: list[tuple[str, Callable[[], int]]] = [
        ("Weighted-binomial divided differences, degrees 1--10", check_divided_differences),
        ("Congruence-preserving bases on negative and positive integers", check_congruences),
        ("Newton reconstruction and Gaussian counterexample", check_newton),
        ("p-adic indicators and two-variable residue synthesis", check_padic_indicators),
        ("Lexicographic finite geometric products", check_geometric_telescoping),
        ("Leading Laurent terms of rational finite differences", check_rational_differences),
        ("Scaled polynomial divided differences", check_scaled_polynomial_difference),
    ]
    total = 0
    for name, check in checks:
        amount = check()
        total += amount
        print(f"PASS: {name} ({amount:,} exact checks)")
    print(f"TOTAL: {total:,} checks passed.")
    print("LIMITATION: these finite checks do not formalize arbitrary Hahn supports,")
    print("class cardinality, arbitrary class homomorphisms, or the complete theorems.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
