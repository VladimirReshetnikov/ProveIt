#!/usr/bin/env python3
"""Exact finite checks for Cardinal Visibility and Normalization.

Requires Python 3.9+ and only the standard library. These checks do not
formalize Hahn support theorems, infinite cardinalities, or class theory.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from random import Random
from typing import Dict, Tuple, TypeVar

E = TypeVar("E")
Exponent = Tuple[int, int, int]
LatticePolynomial = Dict[Exponent, Fraction]
Polynomial = Dict[int, Fraction]


def require(condition: bool, message: str) -> None:
    """Raise even when Python runs with optimization (-O)."""
    if not condition:
        raise AssertionError(message)


def add_term(poly: Dict[E, Fraction], exponent: E, coefficient: Fraction) -> None:
    value = poly.get(exponent, Fraction(0)) + coefficient
    if value:
        poly[exponent] = value
    else:
        poly.pop(exponent, None)


def lattice_product(left: LatticePolynomial, right: LatticePolynomial) -> LatticePolynomial:
    result: LatticePolynomial = {}
    for x, a in left.items():
        for y, b in right.items():
            exponent = (x[0] + y[0], x[1] + y[1], x[2] + y[2])
            add_term(result, exponent, a * b)
    return result


def check_geometric(count: int) -> int:
    # Exponent tuples represent integer combinations of (h, a, b).
    factor = {(0, 1, 0): Fraction(1), (0, 0, 1): Fraction(-1)}
    for n in range(count):
        partial = {(1, -1 - j, j): Fraction(1) for j in range(n + 1)}
        actual = lattice_product(factor, partial)
        expected = {(1, 0, 0): Fraction(1), (1, -n - 1, n + 1): Fraction(-1)}
        require(actual == expected, f"Geometric telescoping failed at N={n}")
    return count


def binomial_half(count: int) -> Dict[int, Fraction]:
    result: Dict[int, Fraction] = {}
    coefficient = Fraction(1)
    for n in range(1, count + 1):
        coefficient *= (Fraction(1, 2) - (n - 1)) / n
        result[n] = coefficient
    return result


def unit_recurrence(count: int) -> Dict[int, Fraction]:
    result = {1: Fraction(1, 2)}
    for n in range(2, count + 1):
        result[n] = -sum((result[j] * result[n - j] for j in range(1, n)), Fraction(0)) / 2
    return result


def check_units(count: int) -> int:
    binomial = binomial_half(count + 1)
    recurrence = unit_recurrence(count)
    require(all(binomial[n] == recurrence[n] for n in range(1, count + 1)),
            "Binomial coefficients disagree with the independent quadratic recurrence")
    require([binomial[n] for n in range(1, 6)] ==
            [Fraction(1, 2), Fraction(-1, 8), Fraction(1, 16),
             Fraction(-5, 128), Fraction(7, 256)], "Printed coefficients are incorrect")
    for n in range(1, count + 1):
        u = {2 * j - 1: binomial[j] for j in range(1, n + 1)}
        # R_N(z) = z U_N(z)^2 + 2 U_N(z) - z.
        residual: Polynomial = {}
        for e, a in u.items():
            for f, b in u.items():
                add_term(residual, e + f + 1, a * b)
            add_term(residual, e, 2 * a)
        add_term(residual, 1, Fraction(-1))
        require(bool(residual), f"Unexpected exact finite root for n={n}")
        require(min(residual) == 2 * n + 1, f"Wrong leading residual exponent for n={n}")
        require(residual[2 * n + 1] == -2 * binomial[n + 1],
                f"Wrong leading residual coefficient for n={n}")
    return count + 2


def sign(value: Fraction) -> int:
    return (value > 0) - (value < 0)


def check_lexicographic(trials: int = 2000) -> int:
    # A finite window of the two arms, ordered by the least active index.
    size = 6
    index_order = [("p", a) for a in reversed(range(size))]
    index_order += [("q", a) for a in range(size)]
    embedding_exponents = [a if arm == "p" else -(a + 1)
                           for arm, a in index_order]
    rng = Random(20260922)
    checks = 0
    for _ in range(trials):
        vector = [Fraction(rng.randint(-12, 12), rng.randint(1, 7))
                  if rng.randrange(3) == 0 else Fraction(0)
                  for _ in index_order]
        first = next((x for x in vector if x), Fraction(0))
        normal_form = {exponent: coefficient
                       for exponent, coefficient in zip(embedding_exponents, vector)
                       if coefficient}
        leading = normal_form[max(normal_form)] if normal_form else Fraction(0)
        require(sign(first) == sign(leading), "Finite surreal exponent embedding changed order")
        checks += 1
    for earlier in range(len(index_order)):
        for later in range(earlier + 1, len(index_order)):
            for n in (1, 2, 100, 10**6):
                vector = [Fraction(0)] * len(index_order)
                vector[earlier] = Fraction(1)
                vector[later] = Fraction(-n)
                first = next(x for x in vector if x)
                require(first > 0, "Later scale did not remain dominated")
                checks += 1
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--terms", type=int, default=32,
                        help="Number of unit-series coefficients (default: 32; range: 5..128)")
    args = parser.parse_args()
    if not 5 <= args.terms <= 128:
        parser.error("--terms must lie between 5 and 128")
    geometric = check_geometric(64)
    units = check_units(args.terms)
    lex = check_lexicographic()
    print(f"PASS: {geometric} finite geometric identities in a symbolic exponent lattice")
    print(f"PASS: {units} unit-series checks ({args.terms} terms plus cross-checks)")
    print(f"PASS: {lex} finite lexicographic and exponent-embedding checks")
    print(f"TOTAL: {geometric + units + lex} exact finite checks passed")
    print("Scope: finite algebra only; no formal verification of infinite/class-sized theorems.")


if __name__ == "__main__":
    main()
