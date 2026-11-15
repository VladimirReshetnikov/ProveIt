#!/usr/bin/env python3
"""Exact reference arithmetic for the finite-descent chapter.

This file is not a proof checker or a formal proof.  Its total descent map
implements formulas whose preservation theorem is proved symbolically in
sections/05_descent.tex.  There cannot be an actual valid square-area input,
so tests cannot execute that branch on a valid counterexample.

Python's gcd/isqrt are convenient implementations of operations that the
paper realizes by bounded primitive-recursive computations.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, isqrt
import json

State = tuple[int, int, int, int]
ZERO_STATE: State = (0, 0, 0, 0)


def square_area_state(state: State) -> bool:
    a, b, c, s = state
    return (min(state) > 0 and a * a + b * b == c * c
            and a * b == 2 * s * s and gcd(a, b) == 1)


def coprime_square_factors(a: int, b: int, c: int) -> tuple[int, int]:
    """Return roots of a,b when gcd(a,b)=1 and ab=c²; default otherwise."""
    if min(a, b, c) <= 0 or gcd(a, b) != 1 or a * b != c * c:
        return (0, 0)
    h = gcd(a, c)
    return (a // h, c // h)


def pythagorean_parameters(a: int, b: int, c: int) -> tuple[int, int, bool]:
    """Parameters of a primitive positive triple, recording the leg swap.

The default on invalid input is (0,0,False).  A valid output satisfies
(even_leg,odd_leg,c)=(2mn,m²−n²,m²+n²).
"""
    if min(a, b, c) <= 0 or gcd(a, b) != 1 or a * a + b * b != c * c:
        return (0, 0, False)
    swapped = bool(a % 2)
    even_leg, odd_leg = (b, a) if swapped else (a, b)
    m = isqrt((c + odd_leg) // 2)
    n = isqrt((c - odd_leg) // 2)
    return (m, n, swapped)


def descend_square_area(state: State) -> State:
    """Total version of the symbolic map (4)--(6) from the paper."""
    if not square_area_state(state):
        return ZERO_STATE
    a, b, c, _ = state
    m, n, _ = pythagorean_parameters(a, b, c)
    r, s = isqrt(m), isqrt(n)
    t, u = isqrt(m + n), isqrt(m - n)
    return ((t + u) // 2, (t - u) // 2, r, s // 2)


def iterate_descent(state: State, fuel: int) -> State:
    """Primitive-recursive iteration with externally supplied fuel."""
    for _ in range(max(0, fuel)):
        state = descend_square_area(state)
    return state


def triangle_to_curve(a, b, c):
    """Map a signed nondegenerate rational right triangle to (n,x,y).

Return None off the domain.  This convention is a decidable default.
"""
    a, b, c = map(Fraction, (a, b, c))
    n = a * b / 2
    if n <= 0 or a * a + b * b != c * c:
        return None
    delta = c - a
    if delta == 0:
        return None  # The proof shows this cannot occur on the stated domain.
    return (n, n * b / delta, 2 * n * n / delta)


def curve_to_triangle(n, x, y):
    """Map E_n,y!=0 to a signed rational triangle; default None elsewhere."""
    n, x, y = map(Fraction, (n, x, y))
    if n <= 0 or y == 0 or y * y != x * (x * x - n * n):
        return None
    return ((x * x - n * n) / y, 2 * n * x / y,
            (x * x + n * n) / y)


def check_examples() -> dict:
    splitting_checks = 0
    for r in range(1, 81):
        for s in range(1, 81):
            if gcd(r, s) == 1:
                assert coprime_square_factors(r * r, s * s, r * s) == (r, s)
                splitting_checks += 1

    parameter_checks = 0
    correspondence_checks = 0
    # Every iteration is explicitly bounded.  All identities use exact rationals.
    for m in range(2, 61):
        for k in range(1, m):
            if gcd(m, k) != 1 or (m - k) % 2 == 0:
                continue
            a, b, c = 2 * m * k, m * m - k * k, m * m + k * k
            assert pythagorean_parameters(a, b, c) == (m, k, False)
            assert pythagorean_parameters(b, a, c) == (m, k, True)
            parameter_checks += 2
            for scale in (Fraction(1), Fraction(2, 3)):
                for sa in (-1, 1):
                    for sc in (-1, 1):
                        triangle = (sa * a * scale, sa * b * scale, sc * c * scale)
                        point = triangle_to_curve(*triangle)
                        assert point is not None
                        assert curve_to_triangle(*point) == triangle
                        n, x, y = point
                        assert y * y == x * x * x - n * n * x
                        assert triangle_to_curve(*curve_to_triangle(*point)) == point
                        correspondence_checks += 1

    known_examples = []
    for n, x, y in ((5, Fraction(25, 4), Fraction(75, 8)),
                    (5, -4, 6), (6, 12, 36), (7, 25, 120)):
        triangle = curve_to_triangle(n, x, y)
        assert triangle is not None
        assert triangle_to_curve(*triangle) == tuple(map(Fraction, (n, x, y)))
        known_examples.append({"n": str(n), "point": [str(x), str(y)],
                               "signed_triangle": list(map(str, triangle))})

    rationals = sorted({Fraction(p, q) for p in range(-12, 13)
                        for q in range(1, 13)})
    finite_points = [(x, y) for x in rationals for y in rationals
                     if y * y == x * x * x - x]
    assert finite_points == [(Fraction(-1), Fraction(0)),
                             (Fraction(0), Fraction(0)),
                             (Fraction(1), Fraction(0))]
    return {
        "status": "all exact arithmetic checks passed",
        "coprime_square_splitting_cases": splitting_checks,
        "pythagorean_parameter_cases": parameter_checks,
        "signed_rational_correspondence_cases": correspondence_checks,
        "known_examples": known_examples,
        "E1_bounded_search": {
            "numerator_bound": 12, "denominator_bound": 12,
            "tested_rational_pairs": len(rationals) ** 2,
            "affine_points": [[str(x), str(y)] for x, y in finite_points],
            "scope": "finite arithmetic sanity check, not the global theorem"
        },
        "descent_branch_scope": (
            "No valid counterexample exists. The preservation and decrease "
            "proofs are symbolic, not established by execution on valid states."
        )
    }


if __name__ == "__main__":
    print(json.dumps(check_examples(), indent=2))
