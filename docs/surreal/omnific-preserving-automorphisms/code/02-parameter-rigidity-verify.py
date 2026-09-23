#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific rigidity article.

Python 3.9+, standard library only. No assertion here tests an infinite
Hahn support theorem, a proper-class claim, or theorem novelty.
Run: python3 verify.py [--output verification.json]
"""
from __future__ import annotations

import argparse
import json
import math
import random
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

Exponent = Tuple[Q, Q, Q]
Polynomial = Dict[Exponent, Q]
ZERO: Exponent = (Q(0), Q(0), Q(0))
SEED = 20260923
COUNTS: Counter = Counter()


def check(name: str, lhs: object, rhs: object) -> None:
    if lhs != rhs:
        raise AssertionError(f"{name}:\nleft={lhs!r}\nright={rhs!r}")
    COUNTS[name] += 1


def clean(p: Polynomial) -> Polynomial:
    return {g: a for g, a in p.items() if a}


def add(*polys: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for p in polys:
        for g, a in p.items():
            out[g] = out.get(g, Q(0)) + a
    return clean(out)


def scale(p: Polynomial, a: Q) -> Polynomial:
    return clean({g: a * b for g, b in p.items()})


def exponent_add(g: Exponent, h: Exponent) -> Exponent:
    return (g[0] + h[0], g[1] + h[1], g[2] + h[2])


def mul(p: Polynomial, q: Polynomial) -> Polynomial:
    out: Polynomial = {}
    for g, a in p.items():
        for h, b in q.items():
            gh = exponent_add(g, h)
            out[gh] = out.get(gh, Q(0)) + a * b
    return clean(out)


def weight(g: Exponent, chi: Exponent) -> Q:
    return sum((g[j] * chi[j] for j in range(3)), Q(0))


def deriv(p: Polynomial, chi: Exponent, n: int = 1) -> Polynomial:
    if n < 0:
        raise ValueError("Derivative order must be nonnegative")
    return clean({g: a * weight(g, chi) ** n for g, a in p.items()})


def divided(p: Polynomial, chi: Exponent, n: int) -> Polynomial:
    return scale(deriv(p, chi, n), Q(1, math.factorial(n)))


def random_exponent(rng: random.Random) -> Exponent:
    return tuple(Q(rng.randint(-3, 3), rng.randint(1, 3)) for _ in range(3))  # type: ignore[return-value]


def random_polynomial(rng: random.Random) -> Polynomial:
    out: Polynomial = {}
    for _ in range(rng.randint(2, 6)):
        g = random_exponent(rng)
        out[g] = out.get(g, Q(0)) + Q(rng.randint(-4, 4), rng.randint(1, 4))
    out = clean(out)
    return out or {ZERO: Q(1)}


def determinant(matrix: Sequence[Sequence[Q]]) -> Q:
    """Exact Gaussian elimination, including row-pivot signs."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Square matrix required")
    a = [list(map(Q, row)) for row in matrix]
    result = Q(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j + 1, n):
            factor = a[i][j] / value
            for k in range(j + 1, n):
                a[i][k] -= factor * a[j][k]
            a[i][j] = Q(0)
    return result


def run() -> dict:
    COUNTS.clear()
    rng = random.Random(SEED)
    max_order = 6
    trials = 72
    for _ in range(trials):
        p = random_polynomial(rng)
        q = random_polynomial(rng)
        chi, eta = random_exponent(rng), random_exponent(rng)
        product = mul(p, q)
        check("Euler product rule", deriv(product, chi),
              add(mul(deriv(p, chi), q), mul(p, deriv(q, chi))))
        check("Commuting Euler operators", deriv(deriv(p, chi), eta),
              deriv(deriv(p, eta), chi))
        for j in range(3):
            check("Largest Laurent exponents add", max(g[j] for g in product),
                  max(g[j] for g in p) + max(g[j] for g in q))
            check("Smallest Laurent exponents add", min(g[j] for g in product),
                  min(g[j] for g in p) + min(g[j] for g in q))
        a, b = Q(rng.randint(-3, 3), 2), Q(rng.randint(-3, 3), 3)
        for n in range(max_order + 1):
            check("Divided Leibniz identity", divided(product, chi, n),
                  add(*(mul(divided(p, chi, r), divided(q, chi, n-r))
                        for r in range(n+1))))
            composed = add(*(scale(divided(divided(p, chi, n-r), chi, r),
                                   a**r * b**(n-r))
                             for r in range(n+1)))
            check("Truncated same-parameter flow composition", composed,
                  scale(divided(p, chi, n), (a+b)**n))
            for r in range(n+1):
                check("Iterative Hasse-Schmidt identity",
                      divided(divided(p, chi, n-r), chi, r),
                      scale(divided(p, chi, n), Q(math.comb(n, r))))
        # A two-parameter coefficient has one finite, exact expression.
        for r in range(5):
            for m in range(5):
                check("Two-parameter flow coefficients",
                      divided(divided(p, chi, m), chi, r),
                      scale(deriv(p, chi, r+m),
                            Q(1, math.factorial(r)*math.factorial(m))))

    # Finite geometric identities do not test any order or infinite limit.
    for _ in range(40):
        a = random_exponent(rng)
        if a == ZERO:
            a = (Q(1), Q(0), Q(0))
        c = random_exponent(rng)
        partial: Polynomial = {}
        for n in range(1, 21):
            g = tuple(c[j] - n*a[j] for j in range(3))
            partial = add(partial, {g: Q((-1)**(n-1))})  # type: ignore[dict-item]
            expected = add({c: Q(1)}, {g: Q((-1)**(n-1))})  # type: ignore[dict-item]
            check("Alternating geometric exact remainder",
                  mul(add({ZERO: Q(1)}, {a: Q(1)}), partial), expected)

    # Independent check of the finite determinant in exponential independence.
    for size in range(1, 8):
        for _ in range(24):
            lambdas = [Q(n, 6) for n in rng.sample(range(-40, 41), size)]
            matrix = [[lam**n for lam in lambdas] for n in range(size)]
            product = Q(1)
            for i in range(size):
                for j in range(i+1, size):
                    product *= lambdas[j] - lambdas[i]
            check("Vandermonde determinant", determinant(matrix), product)
            check("Vandermonde nonsingularity", product != 0, True)

    basis: List[Exponent] = [(Q(1), Q(0), Q(0)),
                            (Q(0), Q(1), Q(0)),
                            (Q(0), Q(0), Q(1))]
    for i, g in enumerate(basis):
        for j, chi in enumerate(basis):
            check("Coordinate derivation test elements", deriv({g: Q(1)}, chi),
                  {g: Q(1)} if i == j else {})

    for n in range(31):
        for r in range(n+1):
            check("Factorial-binomial normalization",
                  Q(math.comb(n, r), math.factorial(n)),
                  Q(1, math.factorial(r)*math.factorial(n-r)))

    return {
        "status": "PASS",
        "arithmetic": "exact fractions; Python standard library only",
        "seed": SEED,
        "random_polynomial_trials": trials,
        "maximum_flow_order": max_order,
        "assertions": sum(COUNTS.values()),
        "by_family": dict(sorted(COUNTS.items())),
        "scope": "Finite coefficient identities and explicit determinants only.",
        "not_verified": [
            "Infinite Hahn support and inverse existence",
            "Root coverage for arbitrary exponent groups",
            "Proper-class assertions",
            "Finite-type embedding theorem or cancellation",
            "Infinite algebraic independence as a quantified theorem",
            "Novelty, peer review, or Lean formalization",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
