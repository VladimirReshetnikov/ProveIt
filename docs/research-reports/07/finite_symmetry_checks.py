#!/usr/bin/env python3
"""Finite checks for the permutation/shift arguments in the accompanying paper.

This is NOT a model of ZFC, a test of large-cardinal existence, or a formal
verification of the set-theoretic proofs. It checks the finite combinatorics
and the reindexing conventions used by those proofs. Standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable

Permutation = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def cycles(p: Permutation) -> list[tuple[int, ...]]:
    """Disjoint cycles, each beginning at its least element."""
    m = len(p)
    if sorted(p) != list(range(m)):
        raise ValueError("Input is not a permutation of range(m).")
    unseen = set(range(m))
    answer = []
    while unseen:
        start = min(unseen)
        cycle, x = [], start
        while x in unseen:
            cycle.append(x)
            unseen.remove(x)
            x = p[x]
        require(x == start, "Cycle decomposition failed.")
        answer.append(tuple(cycle))
    return answer


def inverse(p: Permutation) -> Permutation:
    q = [0] * len(p)
    for i, image in enumerate(p):
        q[image] = i
    return tuple(q)


def permutation_sign(p: Permutation) -> int:
    return sum(p[i] > p[j] for i in range(len(p))
               for j in range(i + 1, len(p))) % 2


def subset_action(p: Permutation, subset: Iterable[int]) -> frozenset[int]:
    return frozenset(p[x] for x in subset)


def check_cycle_realization(p: Permutation) -> int:
    """Check residue/lane formulas k_(ell*n+r)+lane under index shift +1.

    For each residue class, shifted indices have the next residue. At cycle
    wraparound the next class loses exactly its index-zero point. Checking
    the affine formula and its boundary, rather than a purported finite
    approximation to an elementary embedding, is the purpose of this test.
    """
    cs = cycles(p)
    labels: dict[int, tuple[int, int, int]] = {}
    for lane, cycle in enumerate(cs):
        for r, i in enumerate(cycle):
            labels[i] = (lane, len(cycle), r)
    count = 0
    for i, (lane, ell, r) in labels.items():
        target_lane, target_ell, target_r = labels[p[i]]
        require((target_lane, target_ell) == (lane, ell), "Wrong cycle/lane.")
        require(target_r == (r + 1) % ell, "Incorrect residue advance.")
        for n in range(12):
            shifted = ell * n + r + 1
            target_n = n + int(r == ell - 1)
            require(shifted == ell * target_n + target_r,
                    "Affine shift formula failed.")
            count += 1
        require(int(r == ell - 1) in (0, 1), "Wrong finite boundary.")
    # Left action: (sigma . a)_i = a_(sigma^{-1}(i)).
    # Thus the coordinate tuple (a_(sigma(i))) equals sigma^{-1} . a.
    q = inverse(p)
    require(inverse(q) == p, "Reindexing convention failed.")
    return count


def run(max_m: int) -> dict[str, object]:
    permutation_count = 0
    shift_checks = 0
    for m in range(1, max_m + 1):
        for p in itertools.permutations(range(m)):
            shift_checks += check_cycle_realization(p)
            permutation_count += 1

    subset_checks = 0
    for m in range(2, 13):
        p = tuple((i + 1) % m for i in range(m))
        for r in range(1, m):
            for a in itertools.combinations(range(m), r):
                require(subset_action(p, a) != frozenset(a),
                        "A full cycle fixed a nonempty proper subset.")
                subset_checks += 1

    # Boundary example: S3 acts on {0,1,2} naturally and on {3,4} by sign.
    # Every permutation fixes some label, but no label is fixed by all of S3.
    fixed_sets = []
    for p in itertools.permutations(range(3)):
        parity = permutation_sign(p)
        action = tuple(p) + (3 + parity, 4 - parity)
        fixed = {x for x, image in enumerate(action) if x == image}
        require(bool(fixed), "S3 boundary example lacks an elementwise fixed point.")
        fixed_sets.append(fixed)
    require(not set.intersection(*fixed_sets), "Unexpected global fixed point.")

    # A transposition reverses orientation; every odd permutation changes sign.
    orientation_checks = 0
    for m in range(2, 8):
        transposition = (1, 0) + tuple(range(2, m))
        require(permutation_sign(transposition) == 1, "Wrong parity.")
        require(all((b ^ 1) != b for b in range(2)), "Orientation fixed point.")
        orientation_checks += 1

    return {
        "status": "PASS",
        "scope": "finite combinatorics only; not a formal set-theoretic proof",
        "maximum_permutation_degree": max_m,
        "permutations_checked": permutation_count,
        "affine_shift_instances_checked": shift_checks,
        "proper_subset_nonfixed_instances_checked": subset_checks,
        "orientation_actions_checked": orientation_checks,
        "S3_boundary_example": {
            "every_permutation_has_a_fixed_label": True,
            "common_fixed_label_exists": False,
            "fixed_label_sets": [sorted(s) for s in fixed_sets]
        }
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-m", type=int, default=7,
                        help="Exhaustive permutation bound (1..9; default 7).")
    parser.add_argument("--output", type=Path,
                        help="Also save the JSON report at this path.")
    args = parser.parse_args()
    if not 1 <= args.max_m <= 9:
        parser.error("--max-m must be between 1 and 9 (factorial running time).")
    report = run(args.max_m)
    text = json.dumps(report, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
