#!/usr/bin/env python3
"""Finite regression checks for the accompanying research manuscript.

These are exact finite tests of composition conventions and combinatorial
identities. They do not establish singular-cardinal or class-theoretic results.
Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path

Permutation = tuple[int, ...]


def compose(p: Permutation, q: Permutation) -> Permutation:
    """Return p o q, with the right factor applied first."""
    if len(p) != len(q):
        raise ValueError("Permutation sizes must agree")
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: Permutation) -> Permutation:
    if sorted(p) != list(range(len(p))):
        raise ValueError("Input is not a permutation of its coordinate interval")
    result = [0] * len(p)
    for i, value in enumerate(p):
        result[value] = i
    return tuple(result)


def subsets(n: int) -> list[frozenset[int]]:
    return [frozenset(i for i in range(n) if mask & (1 << i))
            for mask in range(1 << n)]


def fixes(p: Permutation, a: frozenset[int]) -> bool:
    return all(p[i] == i for i in a)


def agrees(p: Permutation, q: Permutation, a: frozenset[int]) -> bool:
    return all(p[i] == q[i] for i in a)


def extend_partial(n: int, partial: dict[int, int]) -> Permutation:
    domain = set(partial)
    image = set(partial.values())
    carrier = set(range(n))
    if not domain <= carrier or not image <= carrier or len(image) != len(domain):
        raise ValueError("Expected an injective partial map on the finite carrier")
    extension = dict(partial)
    extension.update(zip(sorted(carrier - domain), sorted(carrier - image)))
    return tuple(extension[i] for i in range(n))


def raw_common_prefix(p: Permutation, q: Permutation) -> frozenset[int]:
    """The predecessor-collection definition, independently of word prefixes."""
    ip, iq = inverse(p), inverse(q)
    result = set()
    for x in range(len(p)):
        pred_p = frozenset(p[:ip[x]])
        pred_q = frozenset(q[:iq[x]])
        if pred_p == pred_q and all(
            (ip[u] < ip[v]) == (iq[u] < iq[v])
            for u in pred_p for v in pred_p
        ):
            result.add(x)
    return frozenset(result)


def run() -> dict[str, object]:
    counts: defaultdict[str, int] = defaultdict(int)
    size_ranges: dict[str, str] = {}

    # All prefix cylinders of permutations up to size 7 are convex intervals.
    for n in range(8):
        words = list(itertools.permutations(range(n)))
        counts["permutations_for_prefix_tests"] += len(words)
        for k in range(n + 1):
            positions: defaultdict[tuple[int, ...], list[int]] = defaultdict(list)
            for index, p in enumerate(words):
                positions[p[:k]].append(index)
            for prefix, indices in positions.items():
                assert len(indices) == math.factorial(n - k)
                assert indices == list(range(indices[0], indices[-1] + 1))
                assert all(words[j][:k] == prefix for j in indices)
                counts["convex_prefix_cylinders"] += 1
    size_ranges["prefix_cylinders"] = "All permutations and all prefix lengths, 0 <= n <= 7"

    # Exact conjugation and both group-uniformity identities, exhaustively.
    for n in range(6):
        words = list(itertools.permutations(range(n)))
        inv = {p: inverse(p) for p in words}
        control_sets = subsets(n)
        for p in words:
            for q in words:
                conjugate = compose(compose(p, q), inv[p])
                left_difference = compose(inv[p], q)
                right_difference = compose(q, inv[p])
                for a in control_sets:
                    pa = frozenset(p[x] for x in a)
                    assert fixes(q, a) == fixes(conjugate, pa)
                    counts["conjugation_identities"] += 1
                    assert fixes(left_difference, a) == agrees(p, q, a)
                    assert fixes(right_difference, a) == agrees(inv[p], inv[q], a)
                    counts["group_uniformity_identities"] += 2
    size_ranges["conjugation_and_uniformities"] = "All pairs and all subsets, 0 <= n <= 5"

    # All finite partial injections up to n=5.
    for n in range(6):
        for domain in subsets(n):
            domain_order = sorted(domain)
            for values in itertools.permutations(range(n), len(domain)):
                partial = dict(zip(domain_order, values))
                p = extend_partial(n, partial)
                assert sorted(p) == list(range(n))
                assert all(p[i] == value for i, value in partial.items())
                counts["partial_injection_extensions"] += 1
    size_ranges["partial_injections"] = "All domains and all injective assignments, 0 <= n <= 5"

    # Independent relation definition of the common labelled prefix.
    for n in range(6):
        words = list(itertools.permutations(range(n)))
        for p in words:
            for q in words:
                k = next((i for i in range(n) if p[i] != q[i]), n)
                d = raw_common_prefix(p, q)
                assert d == frozenset(p[:k])
                if p != q:
                    first_p = next(x for x in p if x not in d)
                    first_q = next(x for x in q if x not in d)
                    assert (first_p < first_q) == (p < q)
                counts["raw_common_prefix_comparisons"] += 1
    size_ranges["raw_common_prefix"] = "All pairs of exhaustive lists, 0 <= n <= 5"

    # Opposite comparison between enumeration order and first relation bit.
    p, q = (0, 1), (1, 0)
    coordinates = [(0, 1), (1, 0), (0, 0), (1, 1)]
    def relation_bits(word: Permutation) -> tuple[bool, ...]:
        inv = inverse(word)
        return tuple(inv[x] < inv[y] for x, y in coordinates)
    assert p < q
    assert relation_bits(q) < relation_bits(p)
    counts["relation_code_reversal_examples"] = 1

    return {
        "status": "PASS",
        "scope": "Exact finite regression tests; not proofs of infinitary theorems",
        "counts": dict(sorted(counts.items())),
        "size_ranges": size_ranges,
        "explicit_exclusions": [
            "Singular-cardinal self-normalization",
            "The cofinality diagonal on the small-subset poset",
            "Non-surjective limits of infinite injections",
            "Class-theoretic existence, comprehension, and replacement",
            "Lean kernel verification",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional output JSON path")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
