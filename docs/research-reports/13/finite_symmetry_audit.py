#!/usr/bin/env python3
"""Finite audit for 'Cyclic symmetry at the ultraexacting boundary'.

This tests periodic incidence words, not large-cardinal existence, arbitrary
infinite words, or the set-theoretic consistency argument. Standard library only.
Run: python3 finite_symmetry_audit.py --max-period 5 --output audit_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import time
from functools import lru_cache
from pathlib import Path
from typing import Iterable

Permutation = tuple[int, ...]
Word = tuple[int, ...]  # nonempty subsets of {0,...,m-1}, represented by bit masks


def compose(p: Permutation, q: Permutation) -> Permutation:
    """p after q, as a left action."""
    return tuple(p[q[i]] for i in range(len(p)))


def parity(p: Permutation) -> int:
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) % 2


def act_mask(p: Permutation, mask: int) -> int:
    return sum(1 << p[i] for i in range(len(p)) if mask & (1 << i))


def act_word(p: Permutation, w: Word) -> Word:
    return tuple(act_mask(p, mask) for mask in w)


def rotations(w: Word) -> set[Word]:
    if not w:
        raise ValueError("The period must be nonempty")
    return {w[k:] + w[:k] for k in range(len(w))}


def primitive(w: Word) -> Word:
    for d in range(1, len(w) + 1):
        if len(w) % d == 0 and w == w[:d] * (len(w) // d):
            return w[:d]
    raise AssertionError("The full length is always a period")


def tail_key(w: Word) -> Word:
    return min(rotations(primitive(w)))


def admissible(w: Word, m: int) -> bool:
    """Infinite repetition has every label, and separates every pair infinitely."""
    return (all(any(mask & (1 << i) for mask in w) for i in range(m)) and
            all(any(bool(mask & (1 << i)) != bool(mask & (1 << j)) for mask in w)
                for i in range(m) for j in range(i + 1, m)))


def subgroup_generated(p: Permutation) -> set[Permutation]:
    identity = tuple(range(len(p)))
    result: set[Permutation] = set()
    q = identity
    while q not in result:
        result.add(q)
        q = compose(p, q)
    assert q == identity
    return result


def stabilizer(w: Word, perms: tuple[Permutation, ...]) -> set[Permutation]:
    rots = rotations(primitive(w))
    return {p for p in perms if act_word(p, primitive(w)) in rots}


def five_action(p: Permutation, label: int) -> int:
    """S3 on 3 natural labels plus 2 orientation labels (3 and 4)."""
    if len(p) != 3 or not 0 <= label < 5:
        raise ValueError("five_action expects a permutation of 3 and a label 0..4")
    return p[label] if label < 3 else 3 + ((label - 3 + parity(p)) % 2)


S3 = tuple(itertools.permutations(range(3)))


@lru_cache(maxsize=None)
def five_label(w: Word) -> int:
    """Construct the paper's rule for periodic patterns using finite lex choice.

    The infinite-word construction instead uses a well-order of real codes.
    This finite routine is rotation invariant and S3 equivariant.
    """
    w = primitive(w)
    if not admissible(w, 3):
        raise ValueError("The incidence word is not admissible")
    base = min(tail_key(act_word(p, w)) for p in S3)
    h = stabilizer(base, S3)
    fixed = [label for label in range(5)
             if all(five_action(p, label) == label for p in h)]
    assert fixed, "The cyclic stabilizer must have a fixed label"
    seed = min(fixed)
    target = tail_key(w)
    outputs = {five_action(p, seed) for p in S3
               if tail_key(act_word(p, base)) == target}
    assert len(outputs) == 1, "Transport must be independent of its witness"
    return outputs.pop()


def periodic_realization(p: Permutation) -> Word:
    """A singleton-incidence periodic word with shift realizing p."""
    unseen = set(range(len(p)))
    cycles: list[list[int]] = []
    while unseen:
        first = min(unseen)
        cycle = [first]
        unseen.remove(first)
        nxt = p[first]
        while nxt != first:
            cycle.append(nxt)
            unseen.remove(nxt)
            nxt = p[nxt]
        cycles.append(cycle)
    from math import lcm
    period_blocks = lcm(*(len(c) for c in cycles))
    return tuple(1 << c[n % len(c)] for n in range(period_blocks) for c in cycles)


def run(max_period: int) -> dict:
    if not 1 <= max_period <= 7:
        raise ValueError("Use a maximum period from 1 through 7")
    started = time.monotonic()
    raw = valid = equivariance = rotation_checks = 0
    unique: set[Word] = set()
    for period in range(1, max_period + 1):
        for w in itertools.product(range(1, 8), repeat=period):
            raw += 1
            if admissible(w, 3):
                valid += 1
                unique.add(tail_key(w))
    orders: dict[str, int] = {}
    for w in sorted(unique, key=lambda x: (len(x), x)):
        h = stabilizer(w, S3)
        assert any(subgroup_generated(p) == h for p in h)
        assert all(compose(p, q) in h for p in h for q in h)
        orders[str(len(h))] = orders.get(str(len(h)), 0) + 1
        value = five_label(w)
        for p in S3:
            assert five_label(act_word(p, w)) == five_action(p, value)
            equivariance += 1
        for r in rotations(w):
            assert five_label(r) == value
            rotation_checks += 1
    # Independently realize every permutation of m for 2 <= m <= 7.
    permutation_tests = 0
    for m in range(2, 8):
        for p in itertools.permutations(range(m)):
            w = periodic_realization(p)
            assert admissible(w, m)
            assert act_word(p, w) in rotations(w)
            permutation_tests += 1
    fixed_counts = []
    for p in S3:
        counts = [label for label in range(5) if five_action(p, label) == label]
        assert counts
        fixed_counts.append({"permutation": list(p), "fixed_labels": counts})
    global_fixed = [label for label in range(5)
                    if all(five_action(p, label) == label for p in S3)]
    assert not global_fixed
    # A 3-cycle excludes the natural 3-point action; a transposition excludes sign.
    assert not any(five_action((1, 2, 0), i) == i for i in range(3))
    assert not any(five_action((1, 0, 2), i) == i for i in (3, 4))
    examples = {}
    for name, w in {
        "three_cycle": (1, 2, 4),
        "transposition": (1, 4, 2, 4),
        "trivial_stabilizer": (1, 1, 2, 4),
    }.items():
        examples[name] = {"word_masks": list(w),
                          "stabilizer_order": len(stabilizer(w, S3)),
                          "output_label": five_label(w)}
    return {
        "status": "PASS",
        "scope": "Finite periodic-word and finite-group audit only; not a formal proof.",
        "maximum_period": max_period,
        "raw_period_words": raw,
        "admissible_period_words": valid,
        "distinct_admissible_tail_patterns": len(unique),
        "stabilizer_order_distribution": orders,
        "equivariance_checks": equivariance,
        "rotation_checks": rotation_checks,
        "permutation_realization_checks_m_2_through_7": permutation_tests,
        "S3_fixed_point_data": fixed_counts,
        "S3_global_fixed_labels": global_fixed,
        "examples": examples,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O: this audit uses assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-period", type=int, default=5)
    parser.add_argument("--output", type=Path, default=Path("audit_results.json"))
    args = parser.parse_args()
    result = run(args.max_period)
    text = json.dumps(result, indent=2)
    args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
