#!/usr/bin/env python3
"""Exact finite regression checks for Local Compactness Forces Arithmetic Rigidity.

These tests do not establish the infinite, topological, or cardinal theorems.
Run: python3 verify.py --output verification_results.json
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random
from typing import Sequence

Point = tuple[tuple[F, ...], int]
Poly = tuple[F, ...]  # coefficients in increasing degree; no trailing zeros


def checked(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def add(a: Point, b: Point) -> Point:
    if len(a[0]) != len(b[0]):
        raise ValueError("Mismatched vector dimensions")
    return tuple(x + y for x, y in zip(a[0], b[0])), a[1] + b[1]


def scale(n: int, a: Point) -> Point:
    return tuple(n * x for x in a[0]), n * a[1]


def less(a: Point, b: Point) -> bool:
    return a[0] < b[0] or (a[0] == b[0] and a[1] < b[1])


def divide(a: Point, m: int) -> tuple[Point, int]:
    if m <= 0:
        raise ValueError("The modulus must be positive")
    q, r = divmod(a[1], m)
    return (tuple(x / m for x in a[0]), q), r


def normalize(p: Sequence[F]) -> Poly:
    result = list(p)
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def p_add(p: Poly, q: Poly) -> Poly:
    return normalize([(p[i] if i < len(p) else F(0)) +
                      (q[i] if i < len(q) else F(0))
                      for i in range(max(len(p), len(q)))])


def p_neg(p: Poly) -> Poly:
    return tuple(-x for x in p)


def p_mul(p: Poly, q: Poly) -> Poly:
    if not p or not q:
        return ()
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return normalize(out)


def p_sign(p: Poly) -> int:
    if not p:
        return 0
    return 1 if p[-1] > 0 else -1


def p_abs(p: Poly) -> Poly:
    return p if p_sign(p) >= 0 else p_neg(p)


def p_less(p: Poly, q: Poly) -> bool:
    return p_sign(p_add(q, p_neg(p))) > 0


def check_division() -> int:
    count = 0
    scalars = [F(-2), F(-1, 2), F(0), F(1, 2), F(2)]
    for d in (1, 2, 3):
        zero = (F(0),) * d
        for vec in product(scalars, repeat=d):
            for n in range(-3, 4):
                a = (vec, n)
                for m in range(1, 8):
                    q, r = divide(a, m)
                    checked(add(scale(m, q), (zero, r)) == a,
                            f"Division identity failed: {a}, {m}")
                    checked(0 <= r < m, "Remainder range failed")
                    if not less(a, (zero, 0)):
                        checked(not less(q, (zero, 0)), "Negative quotient")
                    count += 1
    return count


def check_cooper() -> int:
    rng = random.Random(20261003)
    scalars = [F(-2), F(-1, 2), F(0), F(1, 2), F(2)]
    count = 0
    for d in (1, 2, 3):
        for _ in range(3000):
            a = (tuple(rng.choice(scalars) for _ in range(d)), rng.randrange(-8, 9))
            b = (tuple(rng.choice(scalars) for _ in range(d)), rng.randrange(-8, 9))
            m = rng.randrange(1, 9)
            allowed = {r for r in range(m) if rng.randrange(2)}
            candidates = [(a[0], a[1] + s) for s in range(1, m + 1)]
            finite_test = any(less(a, y) and less(y, b) and y[1] % m in allowed
                              for y in candidates)
            # Independent oracle on Q^d lex Z: distinct vector bounds
            # have a rational midpoint; equal vectors leave an integer interval.
            if not allowed or a[0] > b[0]:
                oracle = False
            elif a[0] < b[0]:
                oracle = True
            else:
                oracle = any(n % m in allowed for n in range(a[1] + 1, b[1]))
            checked(finite_test == oracle, f"Finite-witness mismatch: {a}, {b}, {m}")
            count += 1
    return count


def check_amplification() -> int:
    count = 0
    X: Poly = (F(0), F(1))
    for alpha in (F(1, 2), F(1), F(2)):
        u = (F(0), alpha)
        images: set[Poly] = set()
        for coefficients in product(map(F, (-2, -1, 0, 1, 2)), repeat=4):
            power: Poly = (F(1),)
            image: Poly = ()
            terms: list[Poly] = []
            for r in coefficients:
                term = p_mul(power, normalize((F(0), r)))
                terms.append(term)
                image = p_add(image, term)
                power = p_mul(power, u)
            nonzero = [i for i, r in enumerate(coefficients) if r]
            expected_sign = 0 if not nonzero else (1 if coefficients[nonzero[-1]] > 0 else -1)
            checked(p_sign(image) == expected_sign, "Leading-sign mismatch")
            checked(image not in images, "Finite direct-sum collision")
            images.add(image)
            if nonzero and nonzero[-1] > 0:
                k = nonzero[-1]
                lower: Poly = ()
                for term in terms[:k]:
                    lower = p_add(lower, term)
                checked(p_less(p_abs(lower), p_abs(terms[k])), "Leading domination failed")
            # Multiplication by u moves the one-dimensional subgroup Q X
            # to degree two: a finite illustration of uV intersect V = 0.
            for r in coefficients:
                v = normalize((F(0), r))
                uv = p_mul(u, v)
                checked(not uv or len(uv) == 3, "Unexpected degree after amplification")
            count += 1
        checked(len(images) == 625, "Incorrect image cardinality")
    checked(p_mul(X, X) == (F(0), F(0), F(1)), "X squared failed")
    return count


def check_order_laws() -> int:
    rng = random.Random(601003)
    count = 0
    for d in (1, 2, 3):
        for _ in range(2000):
            points = [(tuple(F(rng.randrange(-6, 7), rng.randrange(1, 5))
                              for _ in range(d)), rng.randrange(-10, 11))
                      for _ in range(3)]
            a, b, c = points
            checked(less(a, b) == less(add(a, c), add(b, c)),
                    "Translation invariance failed")
            checked(sum((less(a, b), a == b, less(b, a))) == 1,
                    "Trichotomy failed")
            if less(a, b) and less(b, c):
                checked(less(a, c), "Transitivity failed")
            count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    results = {
        "status": "PASS",
        "arithmetic": "exact rational arithmetic (fractions.Fraction)",
        "scope": "Finite regression checks only; not a proof of infinite or topological results.",
        "cases": {
            "standard_division": check_division(),
            "coset_invariant_finite_witness": check_cooper(),
            "polynomial_amplification_tuples": check_amplification(),
            "lexicographic_order_triples": check_order_laws(),
        },
    }
    results["total_cases"] = sum(results["cases"].values())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
