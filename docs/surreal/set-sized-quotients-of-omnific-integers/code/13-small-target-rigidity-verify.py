#!/usr/bin/env python3
"""Exact finite checks for the accompanying omnific-integer manuscript.

Python 3.9+, standard library only. No surreal-number implementation is claimed.
Finite polynomials are represented by rational coefficients and tuples of
rational exponents. The order on exponent tuples is lexicographic.

These checks validate finite identities and selected indexing conventions.
They do NOT verify infinite Hahn summability, the small-cut property, class
cardinality assertions, or the manuscript's general theorems.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import permutations
from typing import Dict, Iterable, Tuple

Exponent = Tuple[Q, ...]
Polynomial = Dict[Exponent, Q]


def poly(terms: Iterable[Tuple[Exponent, Q]]) -> Polynomial:
    """Collect equal exponents and remove zero coefficients."""
    result: Polynomial = {}
    dimension = None
    for exponent, coefficient in terms:
        exponent = tuple(Q(v) for v in exponent)
        coefficient = Q(coefficient)
        if dimension is None:
            dimension = len(exponent)
        elif len(exponent) != dimension:
            raise ValueError("Mixed exponent dimensions")
        result[exponent] = result.get(exponent, Q(0)) + coefficient
    return {e: c for e, c in result.items() if c}


def monomial(exponent: Exponent, coefficient: Q = Q(1)) -> Polynomial:
    return poly([(exponent, coefficient)])


def add(*polynomials: Polynomial) -> Polynomial:
    return poly((e, c) for p in polynomials for e, c in p.items())


def scale(p: Polynomial, coefficient: Q) -> Polynomial:
    return poly((e, c * coefficient) for e, c in p.items())


def mul(p: Polynomial, q: Polynomial) -> Polynomial:
    terms = []
    for e, c in p.items():
        for f, d in q.items():
            if len(e) != len(f):
                raise ValueError("Cannot multiply different exponent dimensions")
            terms.append((tuple(a + b for a, b in zip(e, f)), c * d))
    return poly(terms)


def power(p: Polynomial, n: int, dimension: int) -> Polynomial:
    if n < 0:
        raise ValueError("Only nonnegative finite powers are implemented")
    result = monomial((Q(0),) * dimension)
    for _ in range(n):
        result = mul(result, p)
    return result


def require(condition: bool, message: str) -> None:
    # Explicit checks continue to run under python -O.
    if not condition:
        raise AssertionError(message)


def check_geometric() -> None:
    zero = (Q(0), Q(0))
    a = (Q(0), Q(3, 4))
    b = (Q(0), Q(1, 4))
    delta = tuple(s - t for s, t in zip(a, b))
    x = poly([((Q(2), Q(0)), Q(3)), ((Q(1), Q(0)), Q(-2))])
    difference = add(monomial(a), monomial(b, Q(-1)))
    for n in range(51):
        geometric = poly(
            [(tuple(-Q(j) * v for v in delta), Q(1)) for j in range(n + 1)]
        )
        y = mul(mul(x, monomial(tuple(-v for v in a))), geometric)
        require(all(e > zero for e in y), "A truncated quotient has a nonpositive exponent")
        tail = tuple(-Q(n + 1) * v for v in delta)
        rhs = mul(x, add(monomial(zero), monomial(tail, Q(-1))))
        require(mul(difference, y) == rhs, "Finite geometric remainder identity failed")
    print("PASS: 51 exact geometric-remainder identities (N = 0,...,50).")
    print("PASS: all exponents in those 51 truncated quotients are positive.")


def check_cubic_norm() -> None:
    x = monomial((Q(1), Q(0), Q(0)))
    y = monomial((Q(0), Q(1), Q(0)))
    z = monomial((Q(0), Q(0), Q(1)))
    matrix = [[x, scale(z, Q(2)), scale(y, Q(2))],
              [y, x, scale(z, Q(2))],
              [z, y, x]]
    determinant: Polynomial = {}
    for permutation in permutations(range(3)):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(3) for j in range(i + 1, 3))
        term = monomial((Q(0),) * 3, Q((-1) ** inversions))
        for i in range(3):
            term = mul(term, matrix[i][permutation[i]])
        determinant = add(determinant, term)
    expected = add(power(x, 3, 3), scale(power(y, 3, 3), Q(2)),
                   scale(power(z, 3, 3), Q(4)), scale(mul(mul(x, y), z), Q(-6)))
    require(determinant == expected, "Cubic norm determinant failed")
    print("PASS: cubic norm determinant equals x^3 + 2y^3 + 4z^3 - 6xyz.")


def check_boundary_examples() -> None:
    zero = (Q(0),)
    one = monomial(zero)
    t = monomial((Q(1),))
    inverse_t = monomial((Q(-1),))
    # Denominator-free equivalent of X^2 - dY^2 = 1 in the Laurent example.
    plus = add(t, inverse_t)
    minus = add(t, scale(inverse_t, Q(-1)))
    require(add(power(plus, 2, 1), scale(power(minus, 2, 1), Q(-1)))
            == scale(one, Q(4)), "Laurent norm identity failed")
    print("PASS: (T + T^-1)^2 - (T - T^-1)^2 = 4 exactly.")

    x = add(scale(one, Q(3)), scale(t, Q(-1)))
    y = scale(one, Q(2))
    z = t
    value = add(power(add(x, z), 2, 1), scale(power(y, 2, 1), Q(-2)))
    require(value == one, "Rank-deficient example failed")
    print("PASS: (X,Y,Z) = (3-T,2,T) satisfies (X+Z)^2 - 2Y^2 = 1.")

    p = poly([((Q(0),), Q(7)), ((Q(1),), Q(2)), ((Q(3),), Q(-5))])
    q = poly([((Q(0),), Q(-4)), ((Q(2),), Q(3, 7))])
    require(mul(p, q).get(zero, Q(0))
            == p.get(zero, Q(0)) * q.get(zero, Q(0)),
            "Finite constant-coefficient check failed")
    print("PASS: selected positive-support product has multiplicative constant coefficient.")


def main() -> None:
    print("Exact finite checks for Small-Target Rigidity and Arithmetic Specialization")
    print("Standard-library rational arithmetic; no numerical tolerances.\n")
    check_geometric()
    check_cubic_norm()
    check_boundary_examples()
    print("\nAll finite checks passed.")
    print("SCOPE: This is not a Lean proof or a verification of arbitrary Hahn sums,")
    print("surreal cuts, class-size arguments, or the general mathematical theorems.")


if __name__ == "__main__":
    main()
