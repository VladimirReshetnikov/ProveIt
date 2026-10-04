#!/usr/bin/env python3
"""Finite regression checks for the sign-cut and atom-transposition lemmas.

These tests are not proofs of transfinite statements or of set-theoretic schemes.
Python 3.10+, standard library only. Run from any working directory.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from functools import cmp_to_key
from pathlib import Path
from typing import Iterable

SignWord = tuple[int, ...]


def compare(a: SignWord, b: SignWord) -> int:
    """Lexicographic sign order, with termination between -1 and +1."""
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else 0
        y = b[i] if i < len(b) else 0
        if x != y:
            return -1 if x < y else 1
    return 0


def words(depth: int) -> list[SignWord]:
    return [p for n in range(depth + 1)
            for p in itertools.product((-1, 1), repeat=n)]


def separates(p: SignWord, left: Iterable[SignWord],
              right: Iterable[SignWord]) -> bool:
    return all(compare(x, p) < 0 for x in left) and all(
        compare(p, x) < 0 for x in right)


def simplest_cut(left: list[SignWord], right: list[SignWord]) -> SignWord:
    if any(compare(x, y) >= 0 for x in left for y in right):
        raise ValueError("The endpoints do not form a strict cut.")
    bound = max((len(x) + 1 for x in left + right), default=0)
    p: SignWord = ()
    for _ in range(bound + 1):
        l_obstruction = any(compare(p, x) <= 0 for x in left)
        r_obstruction = any(compare(x, p) <= 0 for x in right)
        if l_obstruction and r_obstruction:
            raise AssertionError("A separated cut has opposing obstructions.")
        if not l_obstruction and not r_obstruction:
            return p
        p += (1 if l_obstruction else -1,)
    raise AssertionError("Birthday bound exceeded.")


def audit_cut(left: list[SignWord], right: list[SignWord],
              candidates: list[SignWord]) -> None:
    c = simplest_cut(left, right)
    assert separates(c, left, right)
    bound = max((len(x) + 1 for x in left + right), default=0)
    assert len(c) <= bound
    minima: list[SignWord] = []
    for p in candidates:  # candidates ordered by length
        if len(p) > len(c):
            break
        if separates(p, left, right):
            minima.append(p)
    assert minima == [c], (left, right, c, minima)
    for p in candidates:
        if separates(p, left, right):
            assert p[:len(c)] == c, (left, right, c, p)


def run(depth: int) -> dict[str, object]:
    if not 1 <= depth <= 7:
        raise ValueError("Depth must be between 1 and 7.")
    endpoints = sorted(words(depth), key=cmp_to_key(compare))
    candidates = words(depth + 1)
    interval_count = 0
    # Indices -1 and N encode -infinity and +infinity, respectively.
    for i in range(-1, len(endpoints)):
        for j in range(i + 1, len(endpoints) + 1):
            left = [] if i == -1 else [endpoints[i]]
            right = [] if j == len(endpoints) else [endpoints[j]]
            audit_cut(left, right, candidates)
            interval_count += 1

    small = words(2)
    assignments = separated_assignments = 0
    for labels in itertools.product((0, 1, 2), repeat=len(small)):
        assignments += 1
        left = [s for s, label in zip(small, labels) if label == 1]
        right = [s for s, label in zip(small, labels) if label == 2]
        if all(compare(l, r) < 0 for l in left for r in right):
            audit_cut(left, right, words(3))
            separated_assignments += 1

    negative_checks = 0
    minus_one, zero = (-1,), ()
    for a in range(32):
        nu = (-1,) + (1,) * (a + 1)
        assert compare(minus_one, nu) < 0 < compare(zero, nu)
        for b in range(32):
            nu_b = (-1,) + (1,) * (b + 1)
            assert compare(nu, nu_b) == (a > b) - (a < b)
            negative_checks += 1
        for c in words(6):
            if compare(c, zero) < 0 and compare(nu, c) < 0:
                assert a < len(c)
                negative_checks += 1

    atoms = frozenset(range(7))
    subsets = [frozenset(t) for n in range(3)
               for t in itertools.combinations(atoms, n)]
    swap_checks = 0
    for fixed in subsets:
        for support in subsets:
            for a in support - fixed:
                for b in atoms - (fixed | support):
                    swap = lambda x: b if x == a else a if x == b else x
                    assert frozenset(map(swap, fixed)) == fixed
                    assert frozenset(map(swap, support)) != support
                    swap_checks += 1

    return {
        "status": "PASS",
        "scope": "Finite regression tests only; no transfinite or Lean verification.",
        "endpoint_depth": depth,
        "endpoint_words": len(endpoints),
        "all_endpoint_intervals": interval_count,
        "all_depth_two_assignments": assignments,
        "separated_depth_two_assignments": separated_assignments,
        "negative_code_checks": negative_checks,
        "atom_transposition_checks": swap_checks,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=6)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.depth)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
