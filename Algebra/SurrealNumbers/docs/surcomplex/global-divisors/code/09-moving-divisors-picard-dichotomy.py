#!/usr/bin/env python3
"""Exact finite checks for Global Support Obstructions in Surcomplex Analysis.

Run: python verify_examples.py [--output verification_report.txt]
Requires Python 3.10+ and SymPy. No network or external data are used.
These checks verify illustrative finite identities, not the general theorems.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import Sequence

import sympy as sp

Expr = sp.Expr
u, z, a, t = sp.symbols("u z a t")


def clean(expr: Expr) -> Expr:
    """Canonicalize the rational/polynomial expressions used in the checks."""
    return sp.cancel(sp.expand(expr))


def zero_series(order: int) -> list[Expr]:
    if order < 0:
        raise ValueError("The truncation order must be nonnegative.")
    return [sp.S.Zero for _ in range(order + 1)]


def add(left: Sequence[Expr], right: Sequence[Expr]) -> list[Expr]:
    if len(left) != len(right):
        raise ValueError("Mismatched truncation orders.")
    return [clean(x + y) for x, y in zip(left, right)]


def scale(series: Sequence[Expr], scalar: Expr) -> list[Expr]:
    return [clean(scalar * x) for x in series]


def multiply(left: Sequence[Expr], right: Sequence[Expr]) -> list[Expr]:
    if len(left) != len(right):
        raise ValueError("Mismatched truncation orders.")
    return [clean(sum(left[k] * right[n - k] for k in range(n + 1)))
            for n in range(len(left))]


def power(series: Sequence[Expr], exponent: int) -> list[Expr]:
    if exponent < 0:
        raise ValueError("This helper only supports nonnegative powers.")
    result = zero_series(len(series) - 1)
    result[0] = sp.S.One
    for _ in range(exponent):
        result = multiply(result, series)
    return result


def positive_log(series: Sequence[Expr]) -> list[Expr]:
    """Return log(1 + series) to the supplied t-order; series[0] must be 0."""
    if clean(series[0]) != 0:
        raise ValueError("The logarithm input must have zero constant term.")
    result = zero_series(len(series) - 1)
    product = list(series)
    for n in range(1, len(series)):
        result = add(result, scale(product, sp.Rational((-1) ** (n + 1), n)))
        product = multiply(product, series)
    return result


def positive_exp(series: Sequence[Expr]) -> list[Expr]:
    """Return exp(series) by n e_n = sum(k b_k e_{n-k})."""
    if clean(series[0]) != 0:
        raise ValueError("The exponential input must have zero constant term.")
    result = zero_series(len(series) - 1)
    result[0] = sp.S.One
    for n in range(1, len(series)):
        result[n] = clean(sum(k * series[k] * result[n - k]
                              for k in range(1, n + 1)) / n)
    return result


def compose_polynomial_coefficients(outer: Sequence[Expr],
                                   inner: Sequence[Expr]) -> list[Expr]:
    """Substitute a t-series for z; outer coefficients must be polynomials in z."""
    if len(outer) != len(inner):
        raise ValueError("Mismatched truncation orders.")
    order = len(outer) - 1
    result = zero_series(order)
    max_degree = max([0] + [sp.Poly(c, z).degree() for c in outer if c != 0])
    powers = [power(inner, d) for d in range(int(max_degree) + 1)]
    for index, coeff in enumerate(outer):
        for (degree,), scalar in sp.Poly(coeff, z).terms():
            for n in range(order - index + 1):
                result[n + index] += scalar * powers[degree][n]
    return [clean(c) for c in result]


def require_equal(left: Sequence[Expr], right: Sequence[Expr], name: str) -> None:
    if len(left) != len(right):
        raise AssertionError(f"{name}: mismatched coefficient-array lengths")
    for n, (x, y) in enumerate(zip(left, right)):
        difference = clean(x - y)
        if difference != 0:
            raise AssertionError(f"{name}: nonzero coefficient at t^{n}: {difference}")


def run_checks() -> list[str]:
    report = [
        "EXACT SYMBOLIC VERIFICATION REPORT",
        "Global Support Obstructions in Surcomplex Analysis",
        f"SymPy version: {sp.__version__}",
        "Arithmetic: exact symbolic rational/polynomial operations.",
        "",
    ]

    # 1. A mixed principal part. A finite support is used only for this check.
    order = 6
    perturbation = zero_series(order)
    perturbation[1], perturbation[2], perturbation[3] = 1/u**2, 2/u, -1/u**3
    actual = positive_exp(positive_log(perturbation))
    expected = list(perturbation)
    expected[0] = sp.S.One
    require_equal(actual, expected, "mixed log-exp cancellation")
    report.append("PASS 1: exp(log(1 + t/u^2 + 2t^2/u - t^3/u^3)) "
                  "equals its argument through t^6.")

    # 2. Two finite clusters reproduce their exact polynomial product.
    first, second = zero_series(order), zero_series(order)
    first[1], second[1] = -1/(z-1)**2, -1/(z-2)**3
    exponent = add(positive_log(first), positive_log(second))
    entire = scale(positive_exp(exponent), (z-1)**2 * (z-2)**3)
    target = zero_series(order)
    target[0] = (z-1)**2 * (z-2)**3
    target[1] = -(z-1)**2 - (z-2)**3
    target[2] = sp.S.One
    require_equal(entire, target, "two-cluster pole cancellation")
    report.append("PASS 2: logarithmic construction for clusters (z-1)^2=t and "
                  "(z-2)^3=t gives their polynomial product through t^6.")

    # 3. The Catalan branch of the inverse is checked on both sides.
    order = 7
    identity = zero_series(order)
    identity[0] = z
    quadratic = list(identity)
    quadratic[1] = z**2
    inverse = [(-1)**n * sp.catalan(n) * z**(n+1) for n in range(order+1)]
    require_equal(compose_polynomial_coefficients(quadratic, inverse), identity,
                  "quadratic composed with its inverse")
    require_equal(compose_polynomial_coefficients(inverse, quadratic), identity,
                  "inverse composed with quadratic")
    report.append("PASS 3: Catalan inverse of z+t*z^2 is two-sided through t^7.")

    # 4. No symbolic roots of unity are needed: use a^j as the cluster parameter.
    for degree in range(2, 11):
        complement = sum(a**k * u**(degree-1-k) for k in range(degree))
        if clean((u-a)*complement - (u**degree-a**degree)) != 0:
            raise AssertionError(f"Complement factor failed for degree {degree}")
        if sp.Poly(complement, u).coeff_monomial(u**(degree-2)) != a:
            raise AssertionError("The descending-scale coefficient was not recovered")
    report.append("PASS 4: complementary cluster factors for degrees 2,...,10; "
                  "the next-to-leading coefficient is exactly a.")

    # 5. Finite Lagrange interpolation, followed by positive-support inversion.
    order = 4
    identity = zero_series(order)
    identity[0] = z
    motion = zero_series(order)
    nodes = [1, 2, 3]
    for n, node in enumerate(nodes, start=1):
        lagrange = sp.prod((z-other)/sp.Rational(node-other)
                           for other in nodes if other != node)
        motion[n] = sp.expand(lagrange)
    interpolated = add(identity, motion)
    for n, node in enumerate(nodes, start=1):
        for k in range(order+1):
            expected_value = node if k == 0 else (1 if k == n else 0)
            if clean(interpolated[k].subs(z, node)-expected_value) != 0:
                raise AssertionError("Finite motion interpolation failed")
    correction = zero_series(order)
    for _ in range(order):
        correction = scale(compose_polynomial_coefficients(
            motion, add(identity, correction)), sp.S.NegativeOne)
    inverse = add(identity, correction)
    require_equal(compose_polynomial_coefficients(interpolated, inverse), identity,
                  "interpolated map composed with inverse")
    require_equal(compose_polynomial_coefficients(inverse, interpolated), identity,
                  "inverse composed with interpolated map")
    report.append("PASS 5: one near-identity interpolant sends 1 to 1+t, 2 to 2+t^2, "
                  "3 to 3+t^3; its inverse is two-sided through t^4.")

    # 6. Weierstrass preparation via finite coefficient recursion.
    order, multiplicity = 6, 2
    datum = zero_series(order)
    datum[0], datum[1], datum[2] = u**2, 1+u**3, 2*u+u**4
    A, B = zero_series(order), zero_series(order)
    for n in range(1, order+1):
        h = sp.expand(datum[n] - sum(A[i]*B[n-i] for i in range(1, n)))
        A[n] = sp.rem(h, u**multiplicity, u)
        B[n] = clean((h-A[n])/u**multiplicity)
        if not sp.Poly(B[n], u).is_univariate:
            raise AssertionError("The quotient was not polynomial")
    prepared, unit = list(A), list(B)
    prepared[0], unit[0] = u**multiplicity, sp.S.One
    require_equal(multiply(prepared, unit), datum, "preparation identity")
    report.append("PASS 6: preparation of u^2+t(1+u^3)+t^2(2u+u^4) through t^6.")
    report.append("  Prepared-polynomial corrections A_n:")
    report.extend(f"    n={n}: {sp.sstr(A[n])}" for n in range(1, order+1))

    report.extend([
        "",
        "ALL SIX CHECK GROUPS PASSED.",
        "These are finite symbolic consistency checks only.",
        "The infinite support criteria, stalk/Picard theorems, and dimension "
        "statements are established by the article's written proofs, not this script.",
    ])
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Also write the report to this path.")
    args = parser.parse_args()
    text = "\n".join(run_checks()) + "\n"
    print(text, end="")
    if args.output is not None:
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
