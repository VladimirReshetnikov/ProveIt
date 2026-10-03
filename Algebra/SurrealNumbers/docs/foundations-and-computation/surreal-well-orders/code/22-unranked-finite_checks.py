#!/usr/bin/env python3
"""Deterministic finite regression checks for the accompanying manuscript.

These checks do NOT prove the transfinite, cardinal, or class-model theorems.
Run from the archive root:
    python3 code/finite_checks.py --output data/finite_checks.json
Only the Python standard library is required.
"""
from __future__ import annotations

import argparse
import bisect
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

Word = tuple[int, ...]


def first_difference(x: Sequence[int], y: Sequence[int]) -> int | None:
    """Return the first different coordinate of equal-length words."""
    if len(x) != len(y):
        raise ValueError("The comparison expects equal-length words.")
    return next((i for i, (a, b) in enumerate(zip(x, y)) if a != b), None)


def is_prefix(p: Word, q: Word) -> bool:
    return len(p) <= len(q) and q[:len(p)] == p


def require(condition: bool, section: str, counts: Counter[str]) -> None:
    if not condition:
        raise AssertionError(f"Regression failure in {section}")
    counts[section] += 1


def permutations_and_residuals(counts: Counter[str]) -> dict[str, int]:
    comparisons = 0
    cylinders = 0
    for n in range(1, 8):
        words = list(itertools.permutations(range(n)))
        by_prefix: dict[Word, list[int]] = defaultdict(list)
        for index, word in enumerate(words):
            for k in range(n + 1):
                by_prefix[word[:k]].append(index)
        for prefix, indices in by_prefix.items():
            k = len(prefix)
            residual = tuple(x for x in range(n) if x not in prefix)
            tails = [words[i][k:] for i in indices]
            require(len(indices) == math.factorial(n-k), "residual_cylinders", counts)
            require(indices == list(range(indices[0], indices[-1]+1)),
                    "residual_cylinders", counts)
            require(tails == list(itertools.permutations(residual)),
                    "residual_cylinders", counts)
            cylinders += 1
        if n <= 6:
            for i, x in enumerate(words):
                lower_fibres: dict[int, list[int]] = defaultdict(list)
                for j, y in enumerate(words):
                    k = first_difference(x, y)
                    require((k is None) == (i == j), "first_disagreement", counts)
                    if k is not None:
                        require((x[k] < y[k]) == (i < j),
                                "first_disagreement", counts)
                        if j < i:
                            lower_fibres[k].append(j)
                    comparisons += 1
                # Lower first-disagreement fibres occur in increasing coordinate order.
                concatenated = [j for k in sorted(lower_fibres) for j in lower_fibres[k]]
                require(concatenated == list(range(i)), "disagreement_fibres", counts)
                for k in range(n):
                    smaller = sum(a < x[k] for a in range(n) if a not in x[:k])
                    expected = smaller * math.factorial(n-k-1)
                    require(len(lower_fibres.get(k, [])) == expected,
                            "disagreement_fibres", counts)
    return {"ordered_word_pairs": comparisons, "residual_cylinders": cylinders}


def unranked_injection_tree(counts: Counter[str]) -> dict[str, int]:
    alphabet_size, depth = 6, 4
    words = list(itertools.permutations(range(alphabet_size), depth))
    cylinders: dict[Word, set[int]] = defaultdict(set)
    for index, word in enumerate(words):
        for k in range(depth + 1):
            cylinders[word[:k]].add(index)
    nodes = list(cylinders)
    for p in nodes:
        ancestors = []
        for q in nodes:
            # C(p) subset C(q) precisely when q is a prefix of p.
            included = cylinders[p] <= cylinders[q]
            require(included == is_prefix(q, p), "unranked_inclusion", counts)
            if included and cylinders[p] != cylinders[q]:
                ancestors.append(q)
        ancestors.sort(key=lambda q: -len(cylinders[q]))
        require(ancestors == [p[:k] for k in range(len(p))],
                "unranked_heights", counts)
    # Negative example: without a reserve, appending the forced final label
    # leaves the cylinder unchanged. This is a test of a limitation, not a bug.
    full = list(itertools.permutations(range(4)))
    p, q = (0, 1, 2), (0, 1, 2, 3)
    cp = {w for w in full if is_prefix(p, w)}
    cq = {w for w in full if is_prefix(q, w)}
    require(cp == cq and p != q, "forced_last_label_counterexample", counts)
    return {"alphabet_size": alphabet_size, "depth": depth,
            "words": len(words), "nodes": len(nodes),
            "node_pairs": len(nodes)**2}


def swap_encoding(bits: Iterable[int]) -> Word:
    out: list[int] = []
    for k, bit in enumerate(bits):
        if bit not in (0, 1):
            raise ValueError("Bits must be zero or one.")
        out.extend((2*k, 2*k+1) if bit == 0 else (2*k+1, 2*k))
    return tuple(out)


def pair_swap_traces(counts: Counter[str]) -> dict[str, int]:
    pairs = 4
    all_perms = list(itertools.permutations(range(2*pairs)))
    bits = list(itertools.product((0, 1), repeat=pairs))
    encodings = [swap_encoding(bitword) for bitword in bits]
    for i, e in enumerate(encodings):
        require(tuple(sorted(e)) == tuple(range(2*pairs)), "pair_swap_bijections", counts)
        rank = bisect.bisect_left(all_perms, e)
        # In this finite ambient chain the strict lower trace is determined
        # by its size. Reading the next point then decodes all pair bits.
        recovered = all_perms[rank]
        decoded = tuple(int(recovered[2*k] == 2*k+1) for k in range(pairs))
        require(decoded == bits[i], "pair_swap_trace_decoding", counts)
        for j, f in enumerate(encodings):
            require((e < f) == (bits[i] < bits[j]), "pair_swap_order", counts)
    return {"pairs": pairs, "bitwords": len(bits), "ambient_permutations": len(all_perms)}


def finite_blocks(counts: Counter[str]) -> list[dict[str, int]]:
    result = []
    # Finite block mechanics only; the ambient infinite endpoints are not modeled.
    for n in range(8):
        size = math.factorial(n)
        perms = list(itertools.permutations(range(n)))
        require(len(perms) == size, "finite_blocks", counts)
        interior = max(size-2, 0)
        require(sum(0 < i < size-1 for i in range(size)) == interior,
                "finite_blocks", counts)
        result.append({"tail_size": n, "permutations": size, "interior_points": interior})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/finite_checks.json"))
    args = parser.parse_args()
    counts: Counter[str] = Counter()
    details = {
        "permutations": permutations_and_residuals(counts),
        "unranked_tree": unranked_injection_tree(counts),
        "pair_swaps": pair_swap_traces(counts),
        "finite_blocks": finite_blocks(counts),
    }
    result = {
        "status": "PASS",
        "scope": "Finite regression checks only; not proofs of transfinite or class-theoretic claims.",
        "assertions": dict(sorted(counts.items())),
        "total_assertions": sum(counts.values()),
        "details": details,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
