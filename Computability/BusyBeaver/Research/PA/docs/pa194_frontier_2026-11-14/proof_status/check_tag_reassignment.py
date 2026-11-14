#!/usr/bin/env python3
"""Independent finite checks for the paper tag-reassignment construction.

These checks are supplementary arithmetic tests, not a proof of PA/iPRA
calibration. The universal arguments are in tag_reassignment.tex.
Python 3.10+, standard library only; run with assertions enabled.
"""
from __future__ import annotations

import argparse
from functools import cache
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def recoders(k: int, u: int, e: int):
    assert k >= 4 and 2 <= u < k and 2 <= e < k and u != e
    tags = (0, 1, u, e)
    inverse = {tag: old for old, tag in enumerate(tags)}

    @cache
    def forward(n: int) -> int:
        if n == 0:
            return 0
        ab, r = divmod(n, 4)
        a, b = unpair(ab)
        assert a < n and b < n
        return k * pair(forward(a), forward(b)) + tags[r]

    @cache
    def left_inverse(n: int) -> int:
        if n == 0:
            return 0
        ab, r = divmod(n, k)
        if r not in inverse:
            return 0
        a, b = unpair(ab)
        assert a < n and b < n
        return 4 * pair(left_inverse(a), left_inverse(b)) + inverse[r]

    return forward, left_inverse


def check(k: int, u: int, e: int, bound: int, arity_bound: int) -> dict:
    f, j = recoders(k, u, e)
    values = [f(n) for n in range(bound + 1)]
    assert values[0] == 0 and values[1] == 1
    assert all(v > 0 for v in values[1:])
    assert len(set(values)) == len(values)
    assert all(j(values[n]) == n for n in range(bound + 1))
    inverse_order = next(
        ((a, a + 1, values[a], values[a + 1])
         for a in range(bound) if values[a] > values[a + 1]), None
    )
    tags = (0, 1, u, e)
    cases = 0
    for a in range(arity_bound + 1):
        for b in range(arity_bound + 1):
            for r in range(4):
                old = 4 * pair(a, b) + r
                target = k * pair(f(a), f(b)) + tags[r]
                assert f(old) == target
                cases += 1
            # Quantifier pair order is (body,binder), as in the source.
            old_gamma = 4 * pair(a, 4 * pair(a, a) + 2)
            new_gamma = k * pair(f(a), k * pair(f(a), f(a)) + u)
            assert f(old_gamma) == new_gamma
    swap_involution = None
    if (k, u, e) == (4, 3, 2):
        assert all(f(f(n)) == n for n in range(bound + 1))
        swap_involution = True
    return {
        "k": k, "universal_tag": u, "equality_tag": e,
        "checked_codes_inclusive": [0, bound],
        "constructor_argument_bound_inclusive": arity_bound,
        "constructor_cases": cases,
        "left_inverse": True,
        "finite_injectivity": True,
        "swap_involution": swap_involution,
        "order_reversal_witness": inverse_order,
        "unused_residues": [r for r in range(k) if r not in tags],
        "proof_scope": "finite arithmetic checks only; universal paper argument is separate",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--bound", type=int, default=20000)
    parser.add_argument("--arity-bound", type=int, default=64)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Assertions must remain enabled")
    result = {
        "configurations": [check(*c, args.bound, args.arity_bound)
                           for c in ((4, 3, 2), (5, 2, 4), (6, 2, 4), (8, 2, 4))],
        "source_commit": "32d0d8b7d93a63ad4106c18cdb29b37927acdad2",
        "status": "all finite checks passed",
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
