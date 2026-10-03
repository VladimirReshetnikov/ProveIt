#!/usr/bin/env python3
"""Exact finite diagnostics for the accompanying mathematical article.

Python 3.10+, standard library only. These tests do NOT establish small-cut
saturation, proper-class size, transfinite limits, or a class-theory theorem.
Use: python3 code/finite_checks.py --output data/finite_checks.json
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import cmp_to_key
from itertools import combinations, permutations, product
import json
from pathlib import Path
import random
from typing import Iterable

Word = tuple[int, ...]
SEED = 20261003
COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str, detail: str = "") -> None:
    """Unlike assert, these checks also run under Python's -O option."""
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def sign(value: int) -> int:
    return (value > 0) - (value < 0)


def word_compare(left: Word, right: Word, marker: int) -> int:
    """First disagreement; a missing next letter is the termination marker."""
    for a, b in zip(left, right):
        if a != b:
            return sign(a - b)
    if len(left) == len(right):
        return 0
    n = min(len(left), len(right))
    if len(left) == n:
        return sign(marker - right[n])
    return sign(left[n] - marker)


def prefix_of(prefix: Word, word: Word) -> bool:
    return word[:len(prefix)] == prefix


def prefixes(words: Iterable[Word]) -> set[Word]:
    return {word[:length] for word in words for length in range(len(word) + 1)}


def check_crossing(lower: list[Word], upper: list[Word], marker: int) -> None:
    all_prefixes = prefixes(lower + upper)
    crossing = [p for p in all_prefixes
                if any(prefix_of(p, w) for w in lower)
                and any(prefix_of(p, w) for w in upper)]
    check(bool(crossing), "crossing_nonempty")
    by_length: dict[int, list[Word]] = defaultdict(list)
    for p in crossing:
        by_length[len(p)].append(p)
    check(all(len(ps) == 1 for ps in by_length.values()),
          "crossing_unique_at_length")
    for p, q in combinations(crossing, 2):
        check(prefix_of(p, q) or prefix_of(q, p), "crossing_chain")
    maximal = max(crossing, key=len)
    for w in lower:
        if not prefix_of(maximal, w):
            check(word_compare(w, maximal, marker) < 0, "outside_orientation")
    for w in upper:
        if not prefix_of(maximal, w):
            check(word_compare(maximal, w, marker) < 0, "outside_orientation")
    symbols_lower = [marker if w == maximal else w[len(maximal)]
                     for w in lower if prefix_of(maximal, w)]
    symbols_upper = [marker if w == maximal else w[len(maximal)]
                     for w in upper if prefix_of(maximal, w)]
    check(max(symbols_lower) < min(symbols_upper), "maximal_next_symbols")


def word_tests(rng: random.Random) -> None:
    alphabet = (0, 2, 4)
    all_words = [w for n in range(5) for w in product(alphabet, repeat=n)]
    spaces = {
        "arbitrary": all_words,
        "injective": [w for w in all_words if len(w) == len(set(w))],
        "increasing": [w for w in all_words
                       if all(a < b for a, b in zip(w, w[1:]))],
    }
    for marker in (-1, 1, 3, 5):
        for name, words in spaces.items():
            ordered = sorted(words, key=cmp_to_key(
                lambda x, y: word_compare(x, y, marker)))
            for i, p in enumerate(ordered):
                check(word_compare(p, p, marker) == 0, "word_reflexive")
                for q in ordered[i + 1:]:
                    check(word_compare(p, q, marker) == -1,
                          "word_pair_order", name)
                    check(word_compare(q, p, marker) == 1,
                          "word_pair_reverse", name)
            for p in prefixes(words):
                indices = [i for i, w in enumerate(ordered) if prefix_of(p, w)]
                check(indices == list(range(indices[0], indices[-1] + 1)),
                      "cylinder_convexity", name)
            # Every split gives separated nonempty finite families.
            for split in range(1, len(ordered)):
                check_crossing(ordered[:split], ordered[split:], marker)
            # Sparse families also exercise constraints outside the maximal cylinder.
            for _ in range(120):
                split = rng.randrange(1, len(ordered))
                lower = rng.sample(ordered[:split], min(split, rng.randint(1, 6)))
                upper = rng.sample(ordered[split:],
                                   min(len(ordered) - split, rng.randint(1, 6)))
                check_crossing(lower, upper, marker)
    # Finite mechanism only: a downward extension need not be increasing.
    p = (2, 4, 6, 8)
    q = p + (0,)
    check(len(q) == len(set(q)), "injective_downward_extension")
    check(not all(a < b for a, b in zip(q, q[1:])), "not_increasing_extension")
    check(word_compare(q, p, 1) < 0, "downward_extension_order")
    for n in range(1, len(p)):
        check(word_compare(p[:n], q, 1) < 0, "prefix_below_extension")


def polynomial_compare(p: Word, q: Word) -> int:
    if len(p) != len(q):
        raise ValueError("Coefficient vectors must have equal length.")
    for a, b in zip(reversed(p), reversed(q)):
        if a != b:
            return sign(a - b)
    return 0


def polynomial_tests() -> None:
    base = 3
    for n in range(6):
        vectors = list(product(range(base), repeat=n))
        value = lambda p: sum(c * base ** i for i, c in enumerate(p))
        ordered = sorted(vectors, key=value)
        check([value(p) for p in ordered] == list(range(base ** n)),
              "polynomial_rank_enumeration")
        for p in vectors:
            for q in vectors:
                check(polynomial_compare(p, q) == sign(value(p) - value(q)),
                      "polynomial_comparison")
                for stage in range(n):
                    same = p[stage:] == q[stage:]
                    check(not same or p[stage + 1:] == q[stage + 1:],
                          "tail_equivalence_nested")
        for stage in range(n + 1):
            groups: dict[Word, list[int]] = defaultdict(list)
            for i, p in enumerate(ordered):
                groups[p[stage:]].append(i)
            for tail, indices in groups.items():
                check(indices == list(range(indices[0], indices[-1] + 1)),
                      "tail_class_convexity")
                check(len(indices) == base ** stage, "tail_class_size")
                representative = (0,) * stage + tail
                check(ordered[indices[0]] == representative,
                      "tail_least_representative")
            tails = [p[stage:] for p in ordered
                     if all(x == 0 for x in p[:stage])]
            check(tails == sorted(groups, key=lambda t: tuple(reversed(t))),
                  "quotient_tail_order")


def common_initial_part(p: Word, q: Word) -> frozenset[int]:
    """Finite counterpart of equality/agreement of predecessor classes."""
    ip, iq = {a: i for i, a in enumerate(p)}, {a: i for i, a in enumerate(q)}
    common = set()
    for x in p:
        predecessors_p, predecessors_q = set(p[:ip[x]]), set(q[:iq[x]])
        if predecessors_p != predecessors_q:
            continue
        if all((ip[a] < ip[b]) == (iq[a] < iq[b])
               for a in predecessors_p for b in predecessors_p):
            common.add(x)
    return frozenset(common)


def raw_comparison_tests() -> None:
    for n in range(1, 6):
        orders = list(permutations(range(n)))
        for p in orders:
            for q in orders:
                common = common_initial_part(p, q)
                k = 0
                while k < n and p[k] == q[k]:
                    k += 1
                check(common == frozenset(p[:k]), "raw_common_initial_part")
                comparison = 0 if k == n else sign(p[k] - q[k])
                check(comparison == word_compare(p, q, -1), "raw_comparison")


def diagonal_tests(rng: random.Random) -> None:
    for n in range(1, 25):
        base = list(range(2 * n))
        inputs = []
        for _ in range(n):
            candidate = base.copy()
            rng.shuffle(candidate)
            inputs.append(candidate)
        output = base.copy()
        for i in range(n):
            if output[2 * i] == inputs[i][2 * i]:
                output[2 * i], output[2 * i + 1] = output[2 * i + 1], output[2 * i]
        check(sorted(output) == base, "diagonal_is_permutation")
        for i in range(n):
            check(output[2 * i] != inputs[i][2 * i], "diagonal_disagreement")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/finite_checks.json"))
    args = parser.parse_args()
    rng = random.Random(SEED)
    word_tests(rng)
    polynomial_tests()
    raw_comparison_tests()
    diagonal_tests(rng)
    report = {
        "status": "passed",
        "seed": SEED,
        "total_checks": sum(COUNTS.values()),
        "counts": dict(sorted(COUNTS.items())),
        "scope": "Finite exact mechanisms only; not a transfinite or proper-class proof.",
        "excluded_claims": ["set-cut saturation", "proper-class cardinality",
                            "transfinite limit clauses", "GBC or ETR proof strength",
                            "Lean kernel verification"],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
