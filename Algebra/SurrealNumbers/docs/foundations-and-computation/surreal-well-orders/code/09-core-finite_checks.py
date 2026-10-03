#!/usr/bin/env python3
"""Finite mechanism checks for Well-orders of the Surreal Numbers.

Python 3.10+, standard library only. No finite test verifies a transfinite
statement, a class-theoretic assertion, or a Lean theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from math import factorial
from pathlib import Path
import random
from typing import Iterable, Sequence

SEED = 20261002
Number = int | Fraction


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def require(self, suite: str, condition: bool, message: str) -> None:
        self.counts[suite] += 1
        if not condition:
            raise AssertionError(f"{suite}: {message}")


def first_difference(a: Sequence[Number], b: Sequence[Number]) -> int:
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    raise ValueError("No disagreement before the end of the shorter word")


def complete_prefix(prefix: Sequence[int], alphabet: Sequence[int]) -> tuple[int, ...]:
    if len(set(alphabet)) != len(alphabet):
        raise ValueError("Alphabet contains repeated letters")
    used = set(prefix)
    if len(used) != len(prefix) or not used.issubset(alphabet):
        raise ValueError("Prefix is not an injection into the alphabet")
    return tuple(prefix) + tuple(x for x in alphabet if x not in used)


def support_code(perm: Sequence[int]) -> dict[int, int]:
    if set(perm) != set(range(len(perm))):
        raise ValueError("Not a permutation of an initial finite ordinal")
    return {i: x for i, x in enumerate(perm) if i != x}


def fresh_between(lower: Iterable[Number], upper: Iterable[Number],
                  used: Iterable[Number]) -> Fraction:
    a, b, forbidden = set(lower), set(upper), set(used)
    if a and b:
        lo, hi = Fraction(max(a)), Fraction(min(b))
        if not lo < hi:
            raise ValueError("Strict separation required")
        x = (lo + hi) / 2
        while x in forbidden:
            x = (x + hi) / 2
        return x
    if b:
        return Fraction(min(b | forbidden | {0})) - 1
    return Fraction(max(a | forbidden | {0})) + 1


def forced_separator(lower: Sequence[tuple[int, ...]],
                     upper: Sequence[tuple[int, ...]]) -> tuple[Fraction, ...]:
    """Resolve all finite row comparisons by an injective rational prefix."""
    cross = [first_difference(a, b) for a in lower for b in upper]
    bound = max((d + 1 for d in cross), default=0)
    if any(not a < b for a in lower for b in upper):
        raise ValueError("Rows are not strictly separated")
    active_l, active_u = list(lower), list(upper)
    prefix: list[Fraction] = []
    for index in range(bound + 1):
        if any(index >= len(row) for row in active_l + active_u):
            raise ValueError("Finite rows need a longer common test tail")
        a = {row[index] for row in active_l}
        b = {row[index] for row in active_u}
        common = a & b
        if common:
            if len(common) != 1:
                raise AssertionError("Common active value is not unique")
            x = Fraction(next(iter(common)))
            if x in prefix:
                raise AssertionError("Forced value repeats an earlier value")
            prefix.append(x)
            active_l = [row for row in active_l if row[index] == x]
            active_u = [row for row in active_u if row[index] == x]
        else:
            prefix.append(fresh_between(a, b, prefix))
            return tuple(prefix)
    raise AssertionError("Algorithm exceeded the first-disagreement bound")


def run_checks() -> dict[str, object]:
    check, rng = Checks(), random.Random(SEED)

    # Exhaustive binary words through eight bits, with a shuffled baseline.
    for n in range(9):
        baseline = list(range(2 * n))
        rng.shuffle(baseline)
        pairs = [tuple(sorted(baseline[2*i:2*i+2])) for i in range(n)]
        words = []
        for bits in product((0, 1), repeat=n):
            row = tuple(x for i, bit in enumerate(bits)
                        for x in (pairs[i] if bit == 0 else pairs[i][::-1]))
            check.require("pair_switch", set(row) == set(baseline), "coverage")
            check.require("pair_switch", len(set(row)) == len(row), "injectivity")
            words.append((bits, row))
        for (s, a), (t, b) in combinations(words, 2):
            check.require("pair_switch", (s < t) == (a < b), "lex orientation")

    # Every injective prefix of every length in alphabets of sizes zero to seven.
    for n in range(8):
        alphabet = tuple(range(n))
        for k in range(n + 1):
            for prefix in permutations(alphabet, k):
                completed = complete_prefix(prefix, alphabet)
                code = support_code(completed)
                check.require("prefix_completion", completed[:k] == prefix,
                              "prescribed prefix lost")
                check.require("prefix_completion", set(completed) == set(alphabet),
                              "not exhaustive")
                check.require("prefix_completion", set(code) == set(code.values()),
                              "support not invariant")
                check.require("prefix_completion", all(i != x for i, x in code.items()),
                              "noncanonical fixed point")
                check.require("prefix_completion",
                              tuple(code.get(i, i) for i in alphabet) == completed,
                              "support code does not reconstruct permutation")

    # Sample separated families; all rows have an extra unused final letter.
    separator_cases: list[tuple[list[tuple[int, ...]], list[tuple[int, ...]]]] = []
    for n in range(1, 10):
        for _ in range(120):
            pool: set[tuple[int, ...]] = set()
            target = min(14, factorial(n))
            while len(pool) < target:
                row = list(range(n))
                rng.shuffle(row)
                pool.add(tuple(row) + (n,))
            rows = sorted(pool)
            split = rng.randrange(len(rows) + 1)
            separator_cases.append((rows[:split], rows[split:]))
    separator_cases.append(([], []))
    for n in range(20):
        shared = tuple(range(n))
        separator_cases.append(([shared + (n, n+1)], [shared + (n+1, n)]))
    for lower, upper in separator_cases:
        prefix = forced_separator(lower, upper)
        bound = max((first_difference(a, b) + 1 for a in lower for b in upper),
                    default=0)
        check.require("forced_separator", len(prefix) <= bound + 1, "length bound")
        check.require("forced_separator", len(set(prefix)) == len(prefix),
                      "prefix not injective")
        for a in lower:
            d = first_difference(a, prefix)
            check.require("forced_separator", a[d] < prefix[d], "lower comparison")
        for b in upper:
            d = first_difference(prefix, b)
            check.require("forced_separator", prefix[d] < b[d], "upper comparison")

    # Complete equal-length prefixes in a common enlarged baseline alphabet.
    for n in range(2, 9):
        baseline = list(range(n + 3))
        rng.shuffle(baseline)
        inverse = {x: i for i, x in enumerate(baseline)}
        for _ in range(80):
            k = rng.randrange(1, n)
            a = tuple(rng.sample(range(n), k))
            b = tuple(rng.sample(range(n), k))
            pa = complete_prefix(tuple(inverse[x] for x in a), range(n + 3))
            pb = complete_prefix(tuple(inverse[x] for x in b), range(n + 3))
            ea = tuple(baseline[i] for i in pa)
            eb = tuple(baseline[i] for i in pb)
            check.require("bounded_reflection", ea[:k] == a and eb[:k] == b,
                          "completion changed a prefix")
            check.require("bounded_reflection", (ea < eb) == (a < b),
                          "completion changed comparison")
            if a != b:
                check.require("bounded_reflection",
                              first_difference(ea, eb) == first_difference(a, b),
                              "completion changed first disagreement")

    # Diagonal switch: n rows, n independent baseline pairs, row i defeated at 2i.
    for n in range(1, 31):
        for _ in range(50):
            baseline = list(range(2 * n))
            rng.shuffle(baseline)
            pairs = [tuple(sorted(baseline[2*i:2*i+2])) for i in range(n)]
            rows = []
            for _ in range(n):
                row = list(range(2 * n))
                rng.shuffle(row)
                rows.append(row)
            out = tuple(x for i, pair in enumerate(pairs)
                        for x in (pair[::-1] if rows[i][2*i] == pair[0] else pair))
            check.require("diagonal_switch", set(out) == set(baseline), "coverage")
            for i, row in enumerate(rows):
                check.require("diagonal_switch", out[2*i] != row[2*i],
                              "diagonal failed to defeat row")

    return {
        "status": "PASS",
        "scope": "Finite combinatorial mechanisms only; no transfinite or Lean verification",
        "random_seed": SEED,
        "assertions": dict(sorted(check.counts.items())),
        "total_assertions": sum(check.counts.values()),
        "separator_family_cases": len(separator_cases),
        "exhaustive_ranges": {
            "pair_switch": "all binary words of lengths 0 through 8, all distinct word pairs",
            "prefix_completion": "all injective prefixes on alphabets of sizes 0 through 7"
        }
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data/finite_checks.json")
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
