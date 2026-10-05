#!/usr/bin/env python3
"""Finite regression checks for Beyond Ord.

These check coding/order conventions, not proper-class well-foundedness,
GBC, ETR, or the definability-ceiling theorems. Tail masks are NOT a
simulation of actual condensation in finite orders (all finite intervals
are sets, so actual set-interval condensation is trivial there).

Run: python3 finite_checks.py [--output finite_checks.json]
Only the Python standard library is required.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Tuple

Digits = Tuple[int, ...]  # increasing exponent order
Term = tuple             # decreasing (hereditary exponent, coefficient) pairs


def sign(x: int) -> int:
    return (x > 0) - (x < 0)


def compare_digits(left: Digits, right: Digits) -> int:
    """Compare at the largest differing exponent, padding by zero."""
    for i in range(max(len(left), len(right)) - 1, -1, -1):
        x = left[i] if i < len(left) else 0
        y = right[i] if i < len(right) else 0
        if x != y:
            return sign(x - y)
    return 0


def value(digits: Digits, base: int) -> int:
    if base < 2 or any(not 0 <= d < base for d in digits):
        raise ValueError("Base must be at least 2; digits must lie in [0, base).")
    return sum(d * base**i for i, d in enumerate(digits))


@lru_cache(maxsize=None)
def hereditary(n: int, base: int) -> Term:
    if n < 0 or base < 2:
        raise ValueError("Expected a nonnegative integer and a base at least 2.")
    pairs = []
    exponent = 0
    while n:
        n, coefficient = divmod(n, base)
        if coefficient:
            pairs.append((hereditary(exponent, base), coefficient))
        exponent += 1
    return tuple(reversed(pairs))


def evaluate_term(term: Term, base: int) -> int:
    return sum(base**evaluate_term(exp, base) * coef for exp, coef in term)


def compare_terms(left: Term, right: Term) -> int:
    for (le, lc), (re, rc) in zip(left, right):
        exp_cmp = compare_terms(le, re)
        if exp_cmp:
            return exp_cmp
        if lc != rc:
            return sign(lc - rc)
    return sign(len(left) - len(right))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    rng = random.Random(20261004)
    counts: Counter[str] = Counter()

    def check(name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Failed check in {name}")
        counts[name] += 1

    # Exhaustive base-b finite digit order tests.
    for base in range(2, 6):
        for length in range(5):
            arrays = list(itertools.product(range(base), repeat=length))
            ranked = sorted(arrays, key=lambda v: tuple(reversed(v)))
            for expected, digits in enumerate(ranked):
                check("digit_rank", value(digits, base) == expected)
            for left, right in itertools.product(arrays, repeat=2):
                check("digit_comparison", compare_digits(left, right)
                      == sign(value(left, base) - value(right, base)))

    # Product convention: later exponents form the primary (second) factor.
    for _ in range(10000):
        base = rng.randrange(2, 10)
        p, q = rng.randrange(7), rng.randrange(7)
        x = tuple(rng.randrange(base) for _ in range(p + q))
        low, high = x[:p], x[p:]
        check("support_split", value(x, base)
              == value(low, base) + base**p * value(high, base))
        check("support_split_roundtrip", low + high == x)

    # Flatten a finite-support power of finite-support powers.
    for _ in range(10000):
        base = rng.randrange(2, 8)
        p, q = rng.randrange(1, 6), rng.randrange(1, 6)
        x = tuple(rng.randrange(base) for _ in range(p * q))
        blocks = tuple(x[j*p:(j+1)*p] for j in range(q))
        outer_digits = tuple(value(block, base) for block in blocks)
        check("nested_grouping", value(x, base) == value(outer_digits, base**p))
        check("nested_roundtrip", tuple(d for block in blocks for d in block) == x)

    # Initial exponent support embeddings and canonical tail representatives.
    for _ in range(20000):
        base = rng.randrange(2, 9)
        length = rng.randrange(1, 9)
        cut = rng.randrange(length + 1)
        x = tuple(rng.randrange(base) for _ in range(length))
        y = tuple(rng.randrange(base) for _ in range(length))
        embedded = x[:cut] + (0,) * (length-cut)
        check("initial_support_rank", value(embedded, base) < base**cut)
        rx = (0,) * cut + x[cut:]
        ry = (0,) * cut + y[cut:]
        check("tail_equivalence", (x[cut:] == y[cut:]) == (rx == ry))
        check("tail_representative_minimum", compare_digits(rx, x) <= 0)
        next_cut = rng.randrange(cut, length+1)
        check("tail_refinement", x[cut:] != y[cut:] or x[next_cut:] == y[next_cut:])
        if x[cut:] != y[cut:]:
            check("quotient_order", compare_digits(rx, ry) == compare_digits(x, y))

    # Hereditary normal forms in finite bases, with structural comparison.
    for base in range(2, 7):
        terms = [hereditary(n, base) for n in range(2000)]
        for n, term in enumerate(terms):
            check("hereditary_roundtrip", evaluate_term(term, base) == n)
            check("hereditary_exponents_descend", all(
                compare_terms(term[i][0], term[i+1][0]) > 0
                for i in range(len(term)-1)))
        for _ in range(10000):
            i, j = rng.randrange(len(terms)), rng.randrange(len(terms))
            check("hereditary_comparison", compare_terms(terms[i], terms[j]) == sign(i-j))

    result = {
        "status": "passed",
        "seed": 20261004,
        "counts": dict(sorted(counts.items())),
        "total_assertions": sum(counts.values()),
        "scope": "Finite exact coding and order-convention regression checks only.",
        "not_verified": [
            "proper-class well-foundedness or class/set distinctions",
            "ETR or general condensation existence",
            "inaccessible-cardinal model assumptions",
            "definability ceilings or truth predicates",
            "Lean/Rocq formalization",
        ],
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
