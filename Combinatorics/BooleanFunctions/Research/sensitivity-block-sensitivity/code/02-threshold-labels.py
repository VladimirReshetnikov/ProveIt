#!/usr/bin/env python3
"""Small-instance deterministic label construction by conditional expectation.

The same finite algorithm specifies the theoretical seed, but the seed's
28,800,000,001-row table is not generated here. The guard avoids accidental
attempts to allocate an astronomical instance.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from math import comb
from typing import Mapping

Edge = tuple[int, int]


def cyclic_edges(k: int) -> list[Edge]:
    if type(k) is not int or k < 3 or k % 2 == 0:
        raise ValueError("A cyclic regular tournament needs odd k >= 3")
    return [(i, (i + delta) % k)
            for i in range(k) for delta in range(1, (k + 1) // 2)]


def coherent(vertices: tuple[int, ...] | list[int], edges: list[Edge],
             labels: Mapping[Edge, int]) -> bool:
    inside = set(vertices)
    at_head: dict[int, int] = {}
    for i, j in edges:
        if i in inside and j in inside:
            if j in at_head and at_head[j] != labels[i, j]:
                return False
            at_head[j] = labels[i, j]
    return True


def max_coherent_size(k: int, edges: list[Edge], labels: Mapping[Edge, int]) -> int:
    for size in range(k, 0, -1):
        if any(coherent(I, edges, labels) for I in combinations(range(k), size)):
            return size
    return 0


def conditional_probability(vertices: tuple[int, ...], edges: list[Edge],
                            partial: Mapping[Edge, int], r: int) -> Fraction:
    """Exact probability that this vertex set is coherent after random completion."""
    inside = set(vertices)
    probability = Fraction(1)
    for j in vertices:
        incoming = [(i, h) for i, h in edges if h == j and i in inside]
        known = [partial[e] for e in incoming if e in partial]
        if len(set(known)) > 1:
            return Fraction(0)
        if not incoming:
            continue
        exponent = len(incoming) - len(known) if known else len(incoming) - 1
        probability /= r ** exponent
    return probability


def construct_labels(k: int, r: int, t: int, *, max_rows: int = 15) -> tuple[dict[Edge, int], list[str]]:
    if k > max_rows:
        raise ValueError("This reference implementation is restricted to small label tables")
    if r < 1 or t < 4:
        raise ValueError("Require r >= 1 and t >= 4")
    edges = cyclic_edges(k)
    if comb(k, t) >= r ** (t * (t - 3) // 2):
        raise ValueError("The sufficient union-bound certificate does not hold")
    sets = list(combinations(range(k), t))
    partial: dict[Edge, int] = {}
    def potential() -> Fraction:
        return sum((conditional_probability(I, edges, partial, r) for I in sets), Fraction(0))
    old = potential()
    assert old < 1
    history = [str(old)]
    for edge in edges:
        choices = []
        for label in range(r):
            partial[edge] = label
            choices.append(potential())
        # Conditional expectations average to the pre-assignment expectation.
        assert sum(choices, Fraction(0)) / r == old
        chosen = min(range(r), key=lambda c: (choices[c], c))
        partial[edge] = chosen
        old = choices[chosen]
        history.append(str(old))
    assert old == 0
    assert max_coherent_size(k, edges, partial) < t
    return partial, history
