#!/usr/bin/env python3
"""Exact arithmetic diagnostics for the rational-tangle identity family.

This verifies the integer portion of the construction.  Its topology input
is the separately cited Kauffman--Lambropoulou gluing criterion.  No numerical
approximation or knot invariant is substituted for that theorem.
"""

from __future__ import annotations

import argparse
import itertools
import json
from math import gcd
from pathlib import Path


def act_word(word: str, initial: tuple[int, int]) -> tuple[int, int]:
    """G_word * initial, with G_word multiplied in literal word order."""
    p, q = initial
    for letter in reversed(word):
        if letter == "A":
            p += 2 * q
        elif letter == "B":
            q += 2 * p
        else:
            raise ValueError("letter outside {A,B}")
    return p, q


def normalize(p: int, q: int) -> tuple[int, int]:
    common = gcd(p, q)
    if common != 1:
        raise AssertionError("unimodular program lost primitivity")
    if q < 0 or (q == 0 and p < 0):
        p, q = -p, -q
    return p, q


def act_primitive_program(word: str, base: str) -> tuple[int, int]:
    """Independent Twist/Rot realization used by the proposed PD converter."""
    operations: list[tuple[str, int]]
    if base == "prefix":
        operations = [("T", 1)]
    elif base == "continuation":
        operations = [("T", -2), ("R", 0), ("T", 1)]
    else:
        raise ValueError("unknown base")
    for letter in reversed(word):
        operations.extend(
            [("T", 2)]
            if letter == "A"
            else [("R", 0), ("T", -2), ("R", 0)]
        )
    p, q = 0, 1
    for op, parameter in operations:
        if op == "T":
            p += parameter * q
        else:
            p, q = -q, p
    return normalize(p, q)


def verify_level(m: int) -> dict[str, int | None]:
    words = ["".join(w) for w in itertools.product("AB", repeat=m)]
    prefixes = [act_word(w, (1, 1)) for w in words]
    continuations = [act_word(w, (3, 2)) for w in words]
    assert len(set(prefixes)) == 2**m
    assert len(set(continuations)) == 2**m
    for w, p, q in zip(words, prefixes, continuations):
        assert act_primitive_program(w, "prefix") == p
        assert act_primitive_program(w, "continuation") == q
        assert gcd(*p) == gcd(*q) == 1
        assert p[0] % 2 == p[1] % 2 == 1
        assert q[0] % 2 == 1 and q[1] % 2 == 0
        assert max(p) <= 3**m and max(q) <= 3 ** (m + 1)
    min_off_diagonal: int | None = None
    max_absolute_determinant = 0
    acceptance_count = 0
    for i, (p, q) in enumerate(prefixes):
        for j, (r, s) in enumerate(continuations):
            det = p * s - q * r
            assert det % 2 == 1
            accepted = abs(det) == 1
            assert accepted == (i == j)
            acceptance_count += accepted
            max_absolute_determinant = max(max_absolute_determinant, abs(det))
            if i == j:
                assert det == -1
            else:
                assert abs(det) >= 19
                min_off_diagonal = (
                    abs(det)
                    if min_off_diagonal is None
                    else min(min_off_diagonal, abs(det))
                )
    return {
        "word_length": m,
        "matrix_order": 2**m,
        "entries_checked": 4**m,
        "accepted_entries": acceptance_count,
        "rank_over_every_field_by_identity": 2**m,
        "prefix_crossing_budget": 2 * m + 1,
        "continuation_crossing_budget": 2 * m + 3,
        "closed_crossing_budget": 4 * m + 4,
        "minimum_absolute_off_diagonal": min_off_diagonal,
        "maximum_absolute_determinant": max_absolute_determinant,
        "largest_coordinate_bits": max(
            max(x).bit_length() for x in prefixes + continuations
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=10)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not 0 <= args.max_m <= 12:
        parser.error("use 0 <= max-m <= 12 for an exhaustive finite diagnostic")
    levels = [verify_level(m) for m in range(args.max_m + 1)]
    report = {
        "status": "all exact arithmetic diagnostics passed",
        "scope": "integer identity-family proof diagnostics; topology cited separately",
        "total_entries_checked": sum(x["entries_checked"] for x in levels),
        "levels": levels,
    }
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered)


if __name__ == "__main__":
    main()
