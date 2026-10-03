#!/usr/bin/env python3
"""Finite regression checks for the accompanying research manuscript.

These tests check finite mechanisms only. They do not verify infinite
completion, cardinal regularity, class theory, or any Lean theorem.
Python 3.10+; standard library only; no network access.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from collections import defaultdict
from pathlib import Path
from typing import Iterable, Sequence

Word = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    """Use explicit checks so that running Python with -O remains safe."""
    if not condition:
        raise AssertionError(message)


def first_disagreement_compare(a: Sequence[int], b: Sequence[int]) -> int:
    """End-first lexicographic comparison, using an explicit first difference."""
    for x, y in zip(a, b):
        if x != y:
            return -1 if x < y else 1
    return (len(a) > len(b)) - (len(a) < len(b))


def inverse(p: Sequence[int]) -> Word:
    n = len(p)
    if set(p) != set(range(n)):
        raise ValueError("Expected a permutation of range(len(p)).")
    result = [0] * n
    for i, value in enumerate(p):
        result[value] = i
    return tuple(result)


def prefix_checks(max_n: int = 7) -> dict[str, int]:
    counts = dict(permutations=0, prefix_cylinders=0,
                  child_partitions=0, child_cylinders=0,
                  comparison_pairs=0, coverage_paths=0)
    for n in range(1, max_n + 1):
        permutations = list(itertools.permutations(range(n)))
        counts["permutations"] += len(permutations)
        groups: dict[Word, list[int]] = defaultdict(list)
        for index, word in enumerate(permutations):
            for k in range(n + 1):
                groups[word[:k]].append(index)
            inv = inverse(word)
            require(all(inv[word[i]] == i for i in range(n)),
                    "Inverse identity failed.")
            prefix: Word = ()
            steps = 0
            while len(prefix) < n:
                missing = min(set(range(n)) - set(prefix))
                end = word.index(missing) + 1
                require(end > len(prefix), "Child did not extend its parent.")
                prefix = word[:end]
                steps += 1
                require(set(range(steps)) <= set(prefix),
                        "Least-unused coverage invariant failed.")
            require(prefix == word and steps <= n,
                    "Finite exhaustion path did not terminate correctly.")
            counts["coverage_paths"] += 1

        # Exhaustive pair comparison for n <= 5; adjacent pairs thereafter.
        pairs: Iterable[tuple[Word, Word]]
        pairs = (itertools.product(permutations, repeat=2) if n <= 5
                 else zip(permutations, permutations[1:]))
        for a, b in pairs:
            expected = (a > b) - (a < b)
            require(first_disagreement_compare(a, b) == expected,
                    "First-disagreement comparison disagrees with tuple order.")
            counts["comparison_pairs"] += 1

        for prefix, indices in groups.items():
            counts["prefix_cylinders"] += 1
            require(indices[-1] - indices[0] + 1 == len(indices),
                    "A prefix cylinder was not convex in lexicographic order.")
            remaining = n - len(prefix)
            if remaining == 0:
                continue
            distinguished = min(set(range(n)) - set(prefix))
            children: dict[Word, list[int]] = defaultdict(list)
            for index in indices:
                word = permutations[index]
                end = word.index(distinguished) + 1
                child = word[:end]
                require(child[-1] == distinguished and
                        distinguished not in child[:-1],
                        "Distinguished label was not first hit at the end.")
                children[child].append(index)
            expected_children = sum(math.perm(remaining - 1, k)
                                    for k in range(remaining))
            require(len(children) == expected_children,
                    "Finite child count does not match the permutation sum.")
            covered = [i for child_indices in children.values()
                       for i in child_indices]
            require(sorted(covered) == indices,
                    "Child cylinders did not partition the parent.")
            for child, child_indices in children.items():
                require(child_indices == groups[child],
                        "Child group differs from its full cylinder.")
            counts["child_partitions"] += 1
            counts["child_cylinders"] += len(children)
    return counts


def pair_block_checks(max_pairs: int = 8) -> dict[str, int]:
    words_checked = comparisons = 0
    for n in range(1, max_pairs + 1):
        # The pairs are deliberately not in numerical order as blocks.
        pairs = [(3 * i + 2, 3 * i) for i in reversed(range(n))]
        codes = list(itertools.product((0, 1), repeat=n))
        images: list[Word] = []
        for code in codes:
            image: list[int] = []
            for bit, pair in zip(code, pairs):
                lo, hi = sorted(pair)
                image.extend((lo, hi) if bit == 0 else (hi, lo))
            require(len(set(image)) == 2 * n, "Pair blocks repeat labels.")
            images.append(tuple(image))
            words_checked += 1
        for left, right in zip(images, images[1:]):
            require(left < right, "Binary pair coding was not increasing.")
            comparisons += 1
    return {"binary_words": words_checked, "successive_comparisons": comparisons}


def extend_partial(q: dict[int, int], reserve_count: int = 0) -> dict[int, int]:
    """Extend a finite partial injection on its domain/range plus fresh reserve."""
    if len(set(q.values())) != len(q):
        raise ValueError("The input is not injective.")
    if reserve_count < 0:
        raise ValueError("reserve_count must be nonnegative.")
    support_carrier = set(q) | set(q.values())
    first_fresh = max(support_carrier, default=-1) + 1
    reserve = set(range(first_fresh, first_fresh + reserve_count))
    carrier = support_carrier | reserve
    domain_left = sorted(carrier - set(q))
    range_left = sorted(carrier - set(q.values()))
    require(len(domain_left) == len(range_left), "Residual cardinalities differ.")
    result = dict(q)
    result.update(zip(domain_left, range_left))
    require(set(result) == carrier and set(result.values()) == carrier,
            "Extension is not a permutation of the carrier.")
    require(all(result[k] == v for k, v in q.items()),
            "Extension changed prescribed values.")
    return result


def partial_extension_checks(max_n: int = 5) -> dict[str, int]:
    partial_maps = extensions = 0
    for n in range(max_n + 1):
        for size in range(n + 1):
            for domain in itertools.combinations(range(n), size):
                for image in itertools.permutations(range(n), size):
                    q = dict(zip(domain, image))
                    partial_maps += 1
                    for reserve in (0, 2):
                        extend_partial(q, reserve)
                        extensions += 1
    # Domain and range need not have been subsets of a common initial interval.
    for length in range(1, 21):
        extend_partial({k: k + 1 for k in range(length)}, 3)
        extensions += 1
    return {"partial_injections": partial_maps, "extensions": extensions}


def sign_compare(a: Word, b: Word) -> int:
    """Numerical sign comparison: minus < termination < plus."""
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        if x != y:
            return -1 if x < y else 1
    return 0


def words_of_signs(max_length: int) -> list[Word]:
    return [w for n in range(max_length + 1)
            for w in itertools.product((-1, 1), repeat=n)]


def sign_cone_checks() -> dict[str, int]:
    words = words_of_signs(4)
    tails = words_of_signs(2)
    intervals = extensions = rays = 0
    for a in words:
        for b in words:
            if sign_compare(a, b) >= 0:
                continue
            if len(a) < len(b) and b[:len(a)] == a:
                r = a + (1,) + (-1,) * (len(b) + 1)
            else:
                r = a + (1,)
            intervals += 1
            for tail in tails:
                c = r + tail
                require(sign_compare(a, c) < 0 and sign_compare(c, b) < 0,
                        f"Sign cone failed: {a}, {b}, {c}.")
                extensions += 1
        for tail in tails:
            require(sign_compare(a + (-1,) + tail, a) < 0,
                    "Lower sign cone failed.")
            require(sign_compare(a, a + (1,) + tail) < 0,
                    "Upper sign cone failed.")
            rays += 2
    return {"base_sign_words": len(words), "intervals": intervals,
            "interval_extensions": extensions, "ray_extensions": rays}


def escaping_label_checks() -> dict[str, int]:
    values = inverse_values = 0
    for n in range(101):
        # All nontrivial action lies in the first n+1 positions; the rest is fixed.
        p = tuple(range(1, n + 1)) + (0,) + tuple(range(n + 1, n + 11))
        inv = inverse(p)
        require(inv[0] == n, "The escaped zero has the wrong inverse position.")
        inverse_values += 1
        for k in range(n):
            require(p[k] == k + 1, "Forward shift value failed.")
            values += 1
    return {"forward_values_checked": values, "inverse_positions_checked": inverse_values}


def run() -> dict[str, object]:
    return {
        "status": "PASS",
        "scope": "Finite regression checks only; no transfinite or Lean verification.",
        "prefix_and_exhaustion_tree": prefix_checks(),
        "pair_block_embedding": pair_block_checks(),
        "partial_injection_extension": partial_extension_checks(),
        "sign_cones": sign_cone_checks(),
        "escaping_label": escaping_label_checks(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "finite_checks.json")
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
