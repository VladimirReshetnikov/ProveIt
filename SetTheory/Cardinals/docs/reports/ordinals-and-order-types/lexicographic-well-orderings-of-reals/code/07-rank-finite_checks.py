#!/usr/bin/env python3
"""Reproducible finite illustrations for the accompanying mathematical article.

These tests do NOT verify transfinite induction, choice, cardinal arithmetic,
order topology, representation rank, or any infinite gap classification.
Requires only Python 3.10+ and the standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path
from typing import Iterable, Sequence

Permutation = tuple[int, ...]


def adjacency_criterion(left: Permutation, right: Permutation) -> bool:
    """The article's first-difference criterion on a finite alphabet."""
    if not left < right or sorted(left) != sorted(right):
        return False
    delta = next(i for i, (a, b) in enumerate(zip(left, right)) if a != b)
    unused = sorted(set(left) - set(left[:delta]))
    a, b = left[delta], right[delta]
    return (
        unused.index(b) == unused.index(a) + 1
        and left[delta + 1:] == tuple(sorted(set(unused) - {a}, reverse=True))
        and right[delta + 1:] == tuple(sorted(set(unused) - {b}))
    )


def switch_pairs(bits: Sequence[int]) -> Permutation:
    out: list[int] = []
    for i, bit in enumerate(bits):
        if bit not in (0, 1):
            raise ValueError("A binary word must contain only 0 and 1.")
        out.extend((2 * i, 2 * i + 1) if bit == 0 else (2 * i + 1, 2 * i))
    return tuple(out)


def cut_code(x: int, coordinate_order: Sequence[int]) -> tuple[int, ...]:
    return tuple(int(t < x) for t in coordinate_order)


def is_strictly_increasing(values: Sequence[tuple]) -> bool:
    return all(a < b for a, b in zip(values, values[1:]))


def test_adjacency() -> dict[str, int]:
    adjacent = exhaustive = sampled = 0
    rng = random.Random(20261002)
    for n in range(1, 9):
        perms = list(itertools.permutations(range(n)))
        for left, right in zip(perms, perms[1:]):
            assert adjacency_criterion(left, right), (n, left, right)
            adjacent += 1
        if n <= 5:
            pairs: Iterable[tuple[int, int]] = itertools.combinations(range(len(perms)), 2)
            for i, j in pairs:
                assert adjacency_criterion(perms[i], perms[j]) == (j == i + 1)
                exhaustive += 1
        else:
            for _ in range(10000):
                i, j = sorted(rng.sample(range(len(perms)), 2))
                assert adjacency_criterion(perms[i], perms[j]) == (j == i + 1)
                sampled += 1
    return {"adjacent_pairs": adjacent, "exhaustive_pairs": exhaustive,
            "seeded_sample_pairs": sampled}


def test_pair_switches() -> dict[str, int]:
    words = comparisons = 0
    for n in range(0, 11):
        codes = [switch_pairs(b) for b in itertools.product((0, 1), repeat=n)]
        assert is_strictly_increasing(codes)
        assert len(set(codes)) == 2 ** n
        assert all(sorted(code) == list(range(2 * n)) for code in codes)
        words += len(codes)
        comparisons += max(0, len(codes) - 1)
    return {"words": words, "successive_order_comparisons": comparisons}


def test_cut_codes() -> dict[str, int]:
    coordinate_orders = comparisons = 0
    for n in range(1, 8):
        for order in itertools.permutations(range(n)):
            codes = [cut_code(x, order) for x in range(n)]
            assert is_strictly_increasing(codes), (n, order, codes)
            coordinate_orders += 1
            comparisons += max(0, n - 1)
    return {"coordinate_orders": coordinate_orders, "successive_order_comparisons": comparisons}


def test_disjoint_copy_concatenation() -> dict[str, int]:
    tuples_tested = 0
    for factors in range(1, 4):
        perms = list(itertools.permutations(range(3)))
        images: list[tuple[int, ...]] = []
        for source in itertools.product(perms, repeat=factors):
            # Ordered copies interleave in the ambient alphabet; they are not
            # separated blocks there. They are concatenated only in the code.
            image = tuple(factors * value + i
                          for i, factor in enumerate(source) for value in factor)
            assert sorted(image) == list(range(3 * factors))
            images.append(image)
        assert is_strictly_increasing(images)
        tuples_tested += len(images)
    return {"product_elements": tuples_tested}


def test_ultrafilter_fibers() -> dict[str, object]:
    universe = list(itertools.product((0, 1), repeat=3))
    def principal(i: int) -> list[tuple[int, ...]]:
        return [bits for bits in universe if bits[i]]
    def enumeration(i: int, first: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
        values = principal(i)
        assert first in values
        return (first,) + tuple(x for x in values if x != first)
    a = enumeration(0, (1, 0, 0))
    b = enumeration(1, (1, 1, 0))
    c = enumeration(0, (1, 1, 1))
    assert a < b < c
    assert set(a) == set(c) != set(b)
    return {"nonconvex_fiber_witness_checked": True,
            "universe_size": 3, "enumeration_length": 4}


def run() -> dict[str, object]:
    results = {
        "status": "all finite assertions passed",
        "scope": "Finite illustrations only; no transfinite theorem is machine-verified.",
        "adjacency": test_adjacency(),
        "pair_switch_coding": test_pair_switches(),
        "initial_segment_cut_coding": test_cut_codes(),
        "disjoint_copy_concatenation": test_disjoint_copy_concatenation(),
        "ultrafilter_fibers": test_ultrafilter_fibers(),
    }
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks_results.json"))
    args = parser.parse_args()
    results = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(results, indent=2) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
