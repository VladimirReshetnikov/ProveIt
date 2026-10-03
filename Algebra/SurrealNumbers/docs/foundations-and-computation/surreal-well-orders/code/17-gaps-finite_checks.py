#!/usr/bin/env python3
"""Finite mechanism checks for the accompanying mathematical manuscript.

Standard library only; Python 3.10+. These tests do NOT prove transfinite,
cardinal, class-theoretic, or Lean assertions. Results are deterministic.
Run: python3 finite_checks.py --output finite_checks.json
"""
from __future__ import annotations

import argparse
import itertools as it
import json
from functools import cmp_to_key
from pathlib import Path


def sign_compare(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    """Numerical sign order: minus < termination < plus."""
    for x, y in it.zip_longest(a, b, fillvalue=0):
        if x != y:
            return (x > y) - (x < y)
    return 0


def all_signs(bound: int) -> list[tuple[int, ...]]:
    return [s for n in range(bound + 1) for s in it.product((-1, 1), repeat=n)]


def coefficient_code(s: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(t for v in s for t in (v, v)) + (-1, 1)


def word_code(w: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    return tuple(t for s in w for t in (1,) + coefficient_code(s))


def finite_code_checks() -> dict[str, int]:
    signs = all_signs(4)
    coefficient_pairs = 0
    for a, b in it.product(signs, repeat=2):
        ca, cb = coefficient_code(a), coefficient_code(b)
        assert sign_compare(a, b) == sign_compare(ca, cb)
        if a != b:
            assert ca != cb[:len(ca)] and cb != ca[:len(cb)]
        coefficient_pairs += 1
    alphabet = sorted(all_signs(2), key=cmp_to_key(sign_compare))
    rank = {s: i for i, s in enumerate(alphabet)}
    words = [w for n in range(4) for w in it.product(alphabet, repeat=n)]
    encoded = {w: word_code(w) for w in words}
    keys = {w: tuple(rank[s] for s in w) for w in words}
    word_pairs = 0
    for a, b in it.product(words, repeat=2):
        expected = (keys[a] > keys[b]) - (keys[a] < keys[b])
        assert sign_compare(encoded[a], encoded[b]) == expected
        word_pairs += 1
    return {"coefficient_pairs": coefficient_pairs,
            "words": len(words), "word_pairs": word_pairs}


def predecessor_signature(p: tuple[int, ...], x: int) -> tuple[int, int]:
    """Pred set bitmask and induced strict-relation bitmask; not tuple prefix."""
    n = len(p)
    prior = p[:p.index(x)]
    mask = sum(1 << y for y in prior)
    relation = sum(1 << (y * n + z)
                   for i, y in enumerate(prior) for z in prior[i + 1:])
    return mask, relation


def permutation_checks() -> dict[str, int]:
    comparisons = adjacency_tests = cylinders = cuts_at_levels = 0
    for n in range(0, 8):
        perms = list(it.permutations(range(n)))
        groups: dict[tuple[int, ...], list[int]] = {}
        for index, p in enumerate(perms):
            for length in range(n + 1):
                groups.setdefault(p[:length], []).append(index)
        for indices in groups.values():
            assert indices[-1] - indices[0] + 1 == len(indices)
            cylinders += 1

        if n <= 6:
            signatures = {p: [predecessor_signature(p, x) for x in range(n)]
                          for p in perms}
            for i, p in enumerate(perms):
                for j, q in enumerate(perms):
                    common = {x for x in range(n)
                              if signatures[p][x] == signatures[q][x]}
                    length = 0
                    while length < n and p[length] == q[length]:
                        length += 1
                    assert common == set(p[:length])
                    if i == j:
                        assert len(common) == n
                    else:
                        a = next(x for x in p if x not in common)
                        b = next(x for x in q if x not in common)
                        assert (a < b) == (i < j)
                    comparisons += 1
                    if i < j:
                        a, b = p[length], q[length]
                        residual = set(p[length:])
                        criterion = (
                            not any(a < x < b for x in residual)
                            and p[length + 1:] == tuple(sorted(residual - {a}, reverse=True))
                            and q[length + 1:] == tuple(sorted(residual - {b}))
                        )
                        assert criterion == (j == i + 1)
                        adjacency_tests += 1

        if n <= 5:
            by_length = [[(p, indices[0], indices[-1])
                          for p, indices in groups.items() if len(p) == length]
                         for length in range(n + 1)]
            for split in range(1, len(perms)):
                previous: tuple[int, ...] | None = ()
                for length in range(n + 1):
                    straddlers = [p for p, lo, hi in by_length[length]
                                  if lo < split <= hi]
                    assert len(straddlers) <= 1
                    if straddlers:
                        assert previous is not None
                        assert straddlers[0][:max(0, length - 1)] == previous
                        previous = straddlers[0]
                    else:
                        previous = None
                    cuts_at_levels += 1
    return {"predecessor_comparisons": comparisons,
            "adjacency_pair_checks": adjacency_tests,
            "convex_cylinders": cylinders,
            "cut_level_straddling_checks": cuts_at_levels}


def support_checks() -> dict[str, int]:
    partial_injections = 0
    for n in range(7):
        universe = set(range(n))
        for k in range(n + 1):
            for domain in it.combinations(range(n), k):
                for image in it.permutations(range(n), k):
                    h = dict(zip(domain, image))
                    moved_domain = {x for x in domain if h[x] != x}
                    moved_range = {h[x] for x in moved_domain}
                    necessary = moved_domain | moved_range
                    leftover_inputs = moved_range - moved_domain
                    leftover_outputs = moved_domain - moved_range
                    assert len(leftover_inputs) == len(leftover_outputs)
                    extension = {x: x for x in universe}
                    extension.update({x: h[x] for x in moved_domain})
                    extension.update(zip(sorted(leftover_inputs), sorted(leftover_outputs)))
                    assert set(extension.values()) == universe
                    assert all(extension[x] == y for x, y in h.items())
                    assert {x for x in universe if extension[x] != x} == necessary
                    partial_injections += 1
    return {"partial_injections": partial_injections,
            "maximum_finite_carrier_size": 6}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    result = {
        "status": "all assertions passed",
        "scope": "finite mechanisms only; not transfinite or class-theoretic verification",
        "sign_and_word_codes": finite_code_checks(),
        "permutations_and_cuts": permutation_checks(),
        "finite_support_extension": support_checks(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
