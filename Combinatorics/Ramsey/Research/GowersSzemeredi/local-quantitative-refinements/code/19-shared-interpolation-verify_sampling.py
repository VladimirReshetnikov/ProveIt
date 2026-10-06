#!/usr/bin/env python3
"""Exact finite checks for the sampling and interpolation theorems.

Only the Python standard library is needed.  The proofs are in the article;
these computations detect finite normalization, endpoint, and rounding errors.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial
from pathlib import Path
import json
import random


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def failure_numerator(n, s, r, d):
    """Denominator is binom(n,r); smaller classes require all their points."""
    return sum(choose(s, j) * choose(n-s, r-j)
               for j in range(min(d, s)))


def failure(n, s, r, d):
    return Fraction(failure_numerator(n, s, r, d), choose(n, r))


def minimax(n, q, r, d):
    """Exact max over <=q disjoint classes with total size <=n."""
    weights = [s * failure_numerator(n, s, r, d) for s in range(n+1)]
    previous = [(0, ()) for _ in range(n+1)]
    for _ in range(q):
        current = []
        for budget in range(n+1):
            value, size = max((weights[s] + previous[budget-s][0], s)
                              for s in range(budget+1))
            current.append((value, previous[budget-size][1] + (size,)))
        previous = current
    value, sizes = previous[n]
    return Fraction(value, n * choose(n, r)), sizes


def loss(rows, anchors, d):
    return sum(len(c) for row in rows for c in row
               if len(c & anchors) < min(d, len(c)))


def conditional_loss(rows, n, r, d, anchors):
    a = len(anchors)
    value = Fraction(0)
    for row in rows:
        for c in row:
            have = len(c & anchors)
            need = min(d, len(c)) - have
            if need <= 0:
                continue
            remaining = len(c) - have
            numerator = sum(choose(remaining, j) *
                            choose(n-a-remaining, r-a-j)
                            for j in range(need))
            value += len(c) * Fraction(numerator, choose(n-a, r-a))
    return value


def select_anchors(rows, n, r, d):
    anchors = set()
    history = [conditional_loss(rows, n, r, d, anchors)]
    for _ in range(r):
        options = [(conditional_loss(rows, n, r, d, anchors | {x}), x)
                   for x in range(n) if x not in anchors]
        value, x = min(options)
        assert sum(v for v, _ in options) / len(options) == history[-1]
        assert value <= history[-1]
        anchors.add(x)
        history.append(value)
    assert history[-1] == loss(rows, anchors, d)
    return anchors, history


def lagrange_value(nodes, values, x, p):
    result = 0
    for i, xi in enumerate(nodes):
        numerator = denominator = 1
        for j, xj in enumerate(nodes):
            if i != j:
                numerator = numerator * (x-xj) % p
                denominator = denominator * (xi-xj) % p
        result = (result + values[i] * numerator * pow(denominator, -1, p)) % p
    return result


def polynomial_value(coefficients, x, p):
    return sum(c * pow(x, j, p) for j, c in enumerate(coefficients)) % p


def run():
    counts = {"exact_hypergeometric_cases": 0, "universal_bound_cases": 0,
              "symmetric_minimax_anchor_sets": 0, "interpolation_values": 0}
    for n in range(1, 9):
        for r in range(n+1):
            for d in range(1, 5):
                for s in range(n+1):
                    c = set(range(s))
                    failures = sum(len(c & set(a)) < min(d, s)
                                   for a in combinations(range(n), r))
                    assert failure(n, s, r, d) == Fraction(failures, choose(n, r))
                    counts["exact_hypergeometric_cases"] += 1
                    assert Fraction(s, n) * failure(n, s, r, d) <= Fraction(d, r+1)
                    counts["universal_bound_cases"] += 1
                for q in range(1, 4):
                    value, _ = minimax(n, q, r, d)
                    assert value <= min(Fraction(1), Fraction(q*d, r+1))
                    if r == n:
                        assert value == 0
                    counts["universal_bound_cases"] += 1

    # A complete symmetric family makes every fixed anchor set equally costly.
    n, q, d = 6, 2, 2
    for r in range(n+1):
        value, sizes = minimax(n, q, r, d)
        rows = []
        for pi in permutations(range(n)):
            row, offset = [], 0
            for size in sizes:
                row.append(set(pi[offset:offset+size]))
                offset += size
            rows.append(row)
        for anchors in combinations(range(n), r):
            assert Fraction(loss(rows, set(anchors), d), len(rows)*n) == value
            counts["symmetric_minimax_anchor_sets"] += 1

    rng = random.Random(20261006)
    n, q, r, d = 12, 3, 5, 2
    example_parameters = {"n": n, "q": q, "r": r, "d": d}
    rows = []
    for _ in range(25):
        labels = [rng.randrange(q+1) for _ in range(n)]
        rows.append([{x for x in range(n) if labels[x] == t}
                     for t in range(q)])
    anchors, history = select_anchors(rows, n, r, d)
    assert Fraction(history[-1], len(rows)*n) <= minimax(n, q, r, d)[0]

    # Degree-D row polynomials, including small classes and full-population sampling.
    p = 101
    for degree in range(4):
        coefficients = [rng.randrange(p) for _ in range(degree+1)]
        for size in range(1, 9):
            c = list(range(size))
            nodes = c[:min(size, degree+1)]
            values = [polynomial_value(coefficients, x, p) for x in nodes]
            for x in c:
                assert lagrange_value(nodes, values, x, p) == polynomial_value(coefficients, x, p)
                counts["interpolation_values"] += 1

    # Common-slice interpolation preserves affine degree in each horizontal variable.
    for degree in (1, 2, 3):
        # A(x)+B(x)h1+C(x)h2+D(x)h1h2.
        horizontal_coefficients = [[rng.randrange(p) for _ in range(degree+1)]
                                   for _ in range(4)]
        nodes = list(range(degree+1))
        for h1, h2 in [(0, 0), (1, 2), (7, 9)]:
            def f(x):
                basis = [1, h1, h2, h1*h2]
                return sum(b * polynomial_value(c, x, p)
                           for b, c in zip(basis, horizontal_coefficients)) % p
            values = [f(x) for x in nodes]
            for x in range(11):
                assert lagrange_value(nodes, values, x, p) == f(x)
                counts["interpolation_values"] += 1

    finite_table = []
    for r in (2, 4, 8, 12, 16, 24, 32):
        value, sizes = minimax(32, 3, r, 2)
        finite_table.append({"n": 32, "q": 3, "d": 2, "r": r,
                             "loss_exact": str(value), "loss_decimal": float(value),
                             "maximizing_sizes": sizes,
                             "elementary_bound": float(min(Fraction(1), Fraction(6, r+1)))})
    return {"status": "all checks passed", "counts": counts,
            "greedy_example": {**example_parameters,
                               "anchors": sorted(anchors),
                               "conditional_losses": [str(x) for x in history]},
            "finite_minimax_table": finite_table,
            "scope": "Finite diagnostics; the article contains the general proofs. No Lean kernel check."}


if __name__ == "__main__":
    result = run()
    destination = Path(__file__).with_name("sampling_results.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
