#!/usr/bin/env python3
"""Exact finite checks for Arithmetic Shadows of Omnific Matrix Groups.

Standard-library-only, deterministic, and not a formal proof of the
infinite-support, cardinal, or proper-class theorems. Run with Python 3.10+.
"""
from __future__ import annotations

import json
import random
from fractions import Fraction
from itertools import permutations
from pathlib import Path
from typing import Iterable

Exponent = tuple[Fraction, Fraction]
Poly = dict[Exponent, Fraction]
Matrix = list[list[Poly]]
ORIGIN: Exponent = (Fraction(0), Fraction(0))
COUNTS: dict[str, int] = {}


def monomial(a: int | Fraction, b: int | Fraction,
             c: int | Fraction = 1) -> Poly:
    coefficient = Fraction(c)
    return {(Fraction(a), Fraction(b)): coefficient} if coefficient else {}


def constant(c: int | Fraction) -> Poly:
    return monomial(0, 0, c)


def add(p: Poly, q: Poly) -> Poly:
    out = p.copy()
    for exponent, value in q.items():
        total = out.get(exponent, Fraction(0)) + value
        if total:
            out[exponent] = total
        else:
            out.pop(exponent, None)
    return out


def neg(p: Poly) -> Poly:
    return {e: -c for e, c in p.items()}


def mul(p: Poly, q: Poly) -> Poly:
    if not p or not q:
        return {}
    out: Poly = {}
    for (a, b), c in p.items():
        for (x, y), d in q.items():
            e = (a + x, b + y)
            out[e] = out.get(e, Fraction(0)) + c * d
    return {e: c for e, c in out.items() if c}


def product(polynomials: Iterable[Poly]) -> Poly:
    result = constant(1)
    for polynomial in polynomials:
        result = mul(result, polynomial)
    return result


def identity(n: int) -> Matrix:
    return [[constant(int(i == j)) for j in range(n)] for i in range(n)]


def elementary(n: int, i: int, j: int, p: Poly) -> Matrix:
    if not (0 <= i < n and 0 <= j < n and i != j):
        raise ValueError("Elementary roots require distinct valid indices.")
    result = identity(n)
    result[i][j] = p.copy()
    return result


def mmul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    if len(b) != n:
        raise ValueError("Incompatible matrix dimensions.")
    result: Matrix = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if not a[i][k]:
                continue
            for j in range(n):
                if b[k][j]:
                    result[i][j] = add(result[i][j], mul(a[i][k], b[k][j]))
    return result


def mproduct(matrices: list[Matrix]) -> Matrix:
    if not matrices:
        raise ValueError("A dimension is required for an empty matrix product.")
    result = identity(len(matrices[0]))
    for matrix in matrices:
        result = mmul(result, matrix)
    return result


def ct_matrix(a: Matrix) -> Matrix:
    return [[constant(p.get(ORIGIN, Fraction(0))) for p in row] for row in a]


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(f"Failed check: {name}")
    COUNTS[name] = COUNTS.get(name, 0) + 1


def random_positive_poly(rng: random.Random, allow_constant: bool) -> Poly:
    # Every nonzero exponent is lexicographically positive, including (1,-3).
    exponents = [(0, 1), (0, 2), (1, -3), (1, 0), (2, -1)]
    if allow_constant:
        exponents.append((0, 0))
    p: Poly = {}
    for _ in range(rng.randint(1, 4)):
        a, b = rng.choice(exponents)
        denominator = 1 if (a, b) == (0, 0) else rng.randint(1, 3)
        p = add(p, monomial(a, b, Fraction(rng.randint(-3, 3), denominator)))
    return p


def run() -> dict[str, object]:
    rng = random.Random(20260923)
    parameters = [
        (constant(2), constant(-3)),
        (monomial(1, -2), monomial(0, 1, Fraction(3, 2))),
        (add(monomial(1, -3, -2), monomial(0, 2)), monomial(0, 1, -1)),
        ({}, monomial(1, 0)),
    ]
    for n in range(3, 7):
        for i, j in permutations(range(n), 2):
            for a, b in parameters:
                check("root_additivity", mmul(elementary(n, i, j, a),
                      elementary(n, i, j, b)) == elementary(n, i, j, add(a, b)))
                check("root_inverse", mmul(elementary(n, i, j, a),
                      elementary(n, i, j, neg(a))) == identity(n))
        for i, k, j in permutations(range(n), 3):
            for a, b in parameters:
                comm = mproduct([elementary(n, i, k, a), elementary(n, k, j, b),
                                 elementary(n, i, k, neg(a)),
                                 elementary(n, k, j, neg(b))])
                check("root_commutator", comm == elementary(n, i, j, mul(a, b)))

    for _ in range(200):
        p = random_positive_poly(rng, True)
        q = random_positive_poly(rng, True)
        check("constant_term_multiplication", mul(p, q).get(ORIGIN, 0) ==
              p.get(ORIGIN, 0) * q.get(ORIGIN, 0))
        check("support_nonnegative", all(e >= ORIGIN for e in mul(p, q)))

    for _ in range(40):
        n = 3
        g = identity(n)
        inverse = identity(n)
        for _ in range(4):
            i, j = rng.sample(range(n), 2)
            p = random_positive_poly(rng, True)
            g = mmul(g, elementary(n, i, j, p))
            inverse = mmul(elementary(n, i, j, neg(p)), inverse)
        check("word_inverse", mmul(g, inverse) == identity(n))
        a = random_positive_poly(rng, False)
        b = random_positive_poly(rng, False)
        roots = [elementary(n, 0, 1, a), elementary(n, 1, 2, b),
                 elementary(n, 0, 1, neg(a)), elementary(n, 1, 2, neg(b))]
        conjugates = [mproduct([g, root, inverse]) for root in roots]
        expected = mproduct([g, elementary(n, 0, 2, mul(a, b)), inverse])
        check("conjugated_commutator", mproduct(conjugates) == expected)
        check("conjugated_root_constant_term", ct_matrix(conjugates[0]) == identity(n))
        check("matrix_constant_term_multiplication", ct_matrix(mmul(g, roots[0])) ==
              mmul(ct_matrix(g), ct_matrix(roots[0])))

    d = add(monomial(0, 2), monomial(0, 1, -1))
    for M in range(81):
        Q: Poly = {}
        for r in range(M + 1):
            Q = add(Q, monomial(1, -(r + 2)))
        expected = add(monomial(1, 0), monomial(1, -(M + 1), -1))
        check("geometric_exact_remainder", mul(d, Q) == expected)
        check("geometric_quotient_positive_support", all(e > ORIGIN for e in Q))

    for u in [Fraction(1), Fraction(-1), Fraction(2), Fraction(-3, 2), Fraction(7, 5)]:
        def w(t: Fraction) -> Matrix:
            return mproduct([elementary(2, 0, 1, constant(t)),
                             elementary(2, 1, 0, constant(-1 / t)),
                             elementary(2, 0, 1, constant(t))])
        expected = [[constant(u), {}], [{}, constant(1 / u)]]
        check("two_coordinate_unit_diagonal", mmul(w(u), w(Fraction(-1))) == expected)

    return {
        "status": "PASS",
        "arithmetic": "Exact fractions and finite Laurent polynomials; no floating point",
        "seed": 20260923,
        "checks_by_family": COUNTS,
        "total_checks": sum(COUNTS.values()),
        "scope": "Finite algebraic identities only; no formal verification of infinite or class theorems",
    }


if __name__ == "__main__":
    results = run()
    destination = Path(__file__).with_name("verification_results.json")
    destination.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))
