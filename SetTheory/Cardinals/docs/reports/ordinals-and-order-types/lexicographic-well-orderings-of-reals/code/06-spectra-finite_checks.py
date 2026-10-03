#!/usr/bin/env python3
"""Exhaustive finite sanity checks for the accompanying mathematical article.

Python 3.10+; standard library only. These tests concern finite permutations,
not transfinite proofs. Run:
    python finite_checks.py --output finite_checks_results.json

The default bounds complete without building a quadratic-size comparison table.
Raise bounds cautiously: permutation counts grow factorially.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
from pathlib import Path
from typing import Iterable, Sequence

Word = tuple[int, ...]


def encode_pairs(bits: Iterable[int]) -> Word:
    """Encode bit i in the orientation of pair (2*i, 2*i+1)."""
    out: list[int] = []
    for i, bit in enumerate(bits):
        if bit not in (0, 1):
            raise ValueError(f"Not a binary value: {bit!r}")
        pair = (2 * i, 2 * i + 1)
        out.extend(pair if bit == 0 else pair[::-1])
    return tuple(out)


def first_disagreement(left: Sequence[int], right: Sequence[int]) -> int:
    for i, (a, b) in enumerate(zip(left, right)):
        if a != b:
            return i
    raise ValueError("Inputs agree on their common domain")


def jump_criterion(left: Word, right: Word) -> bool:
    """Finite instance of the theorem, for permutations of one ordered set."""
    if not left < right:
        return False
    d = first_disagreement(left, right)
    available = set(left[d:])
    a, b = left[d], right[d]
    return (
        not any(a < c < b for c in available)
        and left[d + 1:] == tuple(sorted(available - {a}, reverse=True))
        and right[d + 1:] == tuple(sorted(available - {b}))
    )


def check_pair_codes(max_blocks: int) -> dict[str, int]:
    words = comparisons = disagreement_checks = 0
    for m in range(max_blocks + 1):
        bits = list(itertools.product((0, 1), repeat=m))
        encoded = [encode_pairs(word) for word in bits]
        assert len(set(encoded)) == len(bits)
        assert encoded == sorted(encoded)
        for code in encoded:
            assert sorted(code) == list(range(2 * m))
        words += len(bits)
        for i in range(len(bits) - 1):
            assert encoded[i] < encoded[i + 1]
            comparisons += 1
        # Every input pair, not only neighboring strings.
        for i, first in enumerate(bits):
            for j in range(i + 1, len(bits)):
                d = first_disagreement(first, bits[j])
                assert first_disagreement(encoded[i], encoded[j]) == 2 * d
                disagreement_checks += 1
    return {"max_blocks": max_blocks, "encoded_words": words,
            "neighbor_comparisons": comparisons,
            "all_pair_disagreement_checks": disagreement_checks}


def check_prefix_cones(max_n: int) -> dict[str, int]:
    cones = members = 0
    for n in range(max_n + 1):
        perms = list(itertools.permutations(range(n)))
        # Record the first index, last index, and number of members of each cone.
        spans: dict[Word, list[int]] = {}
        for i, perm in enumerate(perms):
            for length in range(n + 1):
                prefix = perm[:length]
                if prefix not in spans:
                    spans[prefix] = [i, i, 0]
                record = spans[prefix]
                record[1] = i
                record[2] += 1
        for prefix, (first, last, count) in spans.items():
            assert count == math.factorial(n - len(prefix))
            assert last - first + 1 == count  # No gaps in the lexicographic list.
            assert all(p[:len(prefix)] == prefix for p in perms[first:last + 1])
            cones += 1
            members += count
    return {"max_alphabet_size": max_n, "prefix_cones": cones,
            "cone_memberships": members}


def check_jumps(max_neighbors_n: int, max_all_pairs_n: int) -> dict[str, int]:
    neighbors = all_pairs = true_jumps = false_jumps = 0
    for n in range(max_neighbors_n + 1):
        perms = list(itertools.permutations(range(n)))
        for left, right in zip(perms, perms[1:]):
            assert jump_criterion(left, right)
            neighbors += 1
        if n <= max_all_pairs_n:
            for i, left in enumerate(perms):
                for j in range(i + 1, len(perms)):
                    predicted = jump_criterion(left, perms[j])
                    adjacent = j == i + 1
                    assert predicted == adjacent, (n, i, j, left, perms[j])
                    all_pairs += 1
                    true_jumps += int(adjacent)
                    false_jumps += int(not adjacent)
    return {"max_neighbor_alphabet_size": max_neighbors_n,
            "max_all_pairs_alphabet_size": max_all_pairs_n,
            "neighbor_checks": neighbors, "all_pair_checks": all_pairs,
            "all_pairs_adjacent": true_jumps,
            "all_pairs_nonadjacent": false_jumps}


def check_initial_segment_codes(max_n: int) -> dict[str, int]:
    orders = vectors = 0
    for n in range(max_n + 1):
        for ordering in itertools.permutations(range(n)):
            seen: set[int] = set()
            codes: list[Word] = []
            # Coordinates have the fixed natural order, unrelated to `ordering`.
            for element in ordering:
                codes.append(tuple(int(z in seen) for z in range(n)))
                seen.add(element)
            assert len(set(codes)) == n
            assert codes == sorted(codes)
            orders += 1
            vectors += n
    return {"max_order_size": max_n, "linear_orders": orders,
            "initial_segment_vectors": vectors}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path("finite_checks_results.json"))
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without Python -O: the checks use assertions.")
    results = {
        "status": "PASS",
        "scope": "Finite combinatorial checks only; no transfinite proof is machine-verified.",
        "python": platform.python_version(),
        "pair_codes": check_pair_codes(8),
        "prefix_cones": check_prefix_cones(7),
        "jump_criterion": check_jumps(8, 6),
        "initial_segment_codes": check_initial_segment_codes(7),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
