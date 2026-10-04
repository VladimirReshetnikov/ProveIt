#!/usr/bin/env python3
"""Exact finite consistency checks accompanying article.tex.

These are convention and implementation tests, not a formal proof of the
infinite algebraic or descriptive-set-theoretic theorems in the article.
Only the Python standard library is used. No numerical surreal evaluation
or floating-point approximation of radicals occurs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, permutations
import json
from math import gcd
from pathlib import Path
import platform
from random import Random
from typing import Iterator, Mapping, Sequence

Exponent = tuple[int, ...]
Polynomial = dict[Exponent, Fraction]


def sign(x: Fraction | int) -> int:
    return (x > 0) - (x < 0)


def group_sign(vector: Sequence[int]) -> int:
    """Highest numbered nonzero rank coordinate decides the sign."""
    for coefficient in reversed(vector):
        if coefficient:
            return sign(coefficient)
    return 0


def leading_sign(poly: Mapping[Exponent, Fraction]) -> int:
    nonzero = {e: c for e, c in poly.items() if c}
    if not nonzero:
        return 0
    leading = max(nonzero, key=lambda e: tuple(reversed(e)))
    return sign(nonzero[leading])


def multiply(left: Mapping[Exponent, Fraction],
             right: Mapping[Exponent, Fraction]) -> Polynomial:
    result: Polynomial = {}
    for e, c in left.items():
        for f, d in right.items():
            if len(e) != len(f):
                raise ValueError("Exponent dimensions must agree")
            g = tuple(a + b for a, b in zip(e, f))
            result[g] = result.get(g, Fraction(0)) + c * d
    return {e: c for e, c in result.items() if c}


def reindex_vector(vector: Sequence[int], positions: Sequence[int],
                   target_dimension: int) -> Exponent:
    if len(vector) != len(positions):
        raise ValueError("One target position is needed per source coordinate")
    if len(set(positions)) != len(positions):
        raise ValueError("Coordinate positions must be distinct")
    if any(p < 0 or p >= target_dimension for p in positions):
        raise ValueError("Target position out of range")
    result = [0] * target_dimension
    for x, p in zip(vector, positions):
        result[p] = x
    return tuple(result)


def reindex_polynomial(poly: Mapping[Exponent, Fraction],
                       positions: Sequence[int],
                       target_dimension: int) -> Polynomial:
    return {reindex_vector(e, positions, target_dimension): c
            for e, c in poly.items()}


def random_polynomial(rng: Random, dimension: int) -> Polynomial:
    result: Polynomial = {}
    for _ in range(rng.randint(1, 11)):
        exponent = tuple(rng.randrange(5) for _ in range(dimension))
        coefficient = Fraction(rng.randint(-9, 9), rng.randint(1, 7))
        result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return {e: c for e, c in result.items() if c}


def rational_enumeration() -> Iterator[Fraction]:
    """Enumerate Q once, by numerator-plus-denominator height and sign."""
    yield Fraction(0)
    height = 2
    while True:
        for denominator in range(1, height):
            numerator = height - denominator
            if gcd(numerator, denominator) == 1:
                q = Fraction(numerator, denominator)
                yield q
                yield -q
        height += 1


def place_order(increasing_labels: Sequence[int]) -> tuple[Fraction, ...]:
    n = len(increasing_labels)
    if sorted(increasing_labels) != list(range(n)):
        raise ValueError("The order must list each label 0,...,n-1 once")
    rank = {label: i for i, label in enumerate(increasing_labels)}
    placed: list[Fraction] = []
    for label in range(n):
        for candidate in rational_enumeration():
            if candidate in placed:
                continue
            if all((placed[i] < candidate) == (rank[i] < rank[label])
                   for i in range(label)):
                placed.append(candidate)
                break
    return tuple(placed)


def colored_embeds_greedy(source: Sequence[int], target: Sequence[int]) -> bool:
    """Color-preserving embeddings of finite chains = subsequences."""
    i = 0
    for color in target:
        if i < len(source) and color == source[i]:
            i += 1
    return i == len(source)


def colored_embeds_bruteforce(source: Sequence[int], target: Sequence[int]) -> bool:
    return any(tuple(target[i] for i in positions) == tuple(source)
               for positions in combinations(range(len(target)), len(source)))


def run(seed: int) -> dict[str, object]:
    rng = Random(seed)
    counts: dict[str, int] = {}

    def check(condition: bool, group: str) -> None:
        if not condition:
            raise AssertionError(f"Check failed in group {group}")
        counts[group] = counts.get(group, 0) + 1

    for dimension in range(1, 6):
        for _ in range(500):
            larger = dimension + rng.randrange(1, 5)
            positions = sorted(rng.sample(range(larger), dimension))
            v = tuple(rng.randint(-8, 8) for _ in range(dimension))
            w = tuple(rng.randint(-8, 8) for _ in range(dimension))
            difference = tuple(x - y for x, y in zip(v, w))
            image_v = reindex_vector(v, positions, larger)
            image_w = reindex_vector(w, positions, larger)
            image_difference = tuple(x - y for x, y in zip(image_v, image_w))
            check(group_sign(difference) == group_sign(image_difference),
                  "ordered_group_reindexing")
            check(reindex_vector(difference, positions, larger) == image_difference,
                  "ordered_group_additivity")

    for dimension in range(1, 5):
        for _ in range(350):
            p = random_polynomial(rng, dimension)
            q = random_polynomial(rng, dimension)
            pq = multiply(p, q)
            check(leading_sign(pq) == leading_sign(p) * leading_sign(q),
                  "polynomial_product_sign")
            larger = dimension + rng.randrange(1, 4)
            positions = sorted(rng.sample(range(larger), dimension))
            image_p = reindex_polynomial(p, positions, larger)
            image_q = reindex_polynomial(q, positions, larger)
            check(leading_sign(image_p) == leading_sign(p),
                  "polynomial_reindex_sign")
            check(reindex_polynomial(pq, positions, larger) ==
                  multiply(image_p, image_q), "polynomial_reindex_product")

    # Explicit cancellation and an intentionally reversed rank orientation.
    one = {(0, 0): Fraction(1)}
    p = {(1, 0): Fraction(1), (0, 0): Fraction(1)}
    q = {(1, 0): Fraction(1), (0, 0): Fraction(-1)}
    check(multiply(p, q) == {(2, 0): Fraction(1), (0, 0): Fraction(-1)},
          "explicit_cancellation")
    check(multiply(one, p) == p, "explicit_cancellation")
    witness = (-1, 1)
    check(group_sign(witness) == 1 and
          group_sign(reindex_vector(witness, (1, 0), 2)) == -1,
          "orientation_negative_control")

    # All finite labeled linear orders up to size 7.
    for n in range(8):
        for order in permutations(range(n)):
            points = place_order(order)
            rank = {label: i for i, label in enumerate(order)}
            check(len(set(points)) == n and
                  all((points[i] < points[j]) == (rank[i] < rank[j])
                      for i in range(n) for j in range(n)),
                  "rational_placement_all_orders_le_7")

    for _ in range(2400):
        m, n = rng.randrange(6), rng.randrange(8)
        source = tuple(rng.randrange(4) for _ in range(m))
        target = tuple(rng.randrange(4) for _ in range(n))
        check(colored_embeds_greedy(source, target) ==
              colored_embeds_bruteforce(source, target),
              "finite_colored_chain_embeddings")
        check(colored_embeds_bruteforce((0,) * m, (0,) * n) == (m <= n),
              "finite_uncolored_chain_embeddings")

    # Orthogonality of sign characters on (Z/2Z)^m.
    # This checks the finite averaging operation used to isolate radical terms.
    for m in range(7):
        size = 1 << m
        for a in range(size):
            for b in range(size):
                total = sum((-1 if ((a ^ b) & flip).bit_count() % 2 else 1)
                            for flip in range(size))
                check(total == (size if a == b else 0),
                      "multiquadratic_character_orthogonality")

    return {
        "status": "PASS",
        "seed": seed,
        "python_version": platform.python_version(),
        "checks_by_group": counts,
        "total_checks": sum(counts.values()),
        "arithmetic": "integers and exact fractions; no floating point",
        "scope": "Finite convention/implementation checks only; not a formal proof",
        "max_finite_order_size": 7,
        "max_radical_character_rank": 6,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261003)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.seed)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
