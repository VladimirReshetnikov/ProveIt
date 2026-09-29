#!/usr/bin/env python3
"""Finite checks accompanying the surreal gap-spectrum manuscript.

These tests verify finite syntax and bookkeeping only. They do not verify
freshness, forcing, infinite cofinality, saturation, or proper-class arguments.
Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Iterable

Sign = tuple[int, ...]


def check(condition: bool, message: str) -> None:
    """Keep checks active even when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def signs(max_length: int) -> Iterable[Sign]:
    if max_length < 0:
        raise ValueError("max_length must be nonnegative")
    for length in range(max_length + 1):
        yield from itertools.product((-1, 1), repeat=length)


def compare(left: Sign, right: Sign) -> int:
    """Surreal sign order: a missing entry lies between minus and plus."""
    for index in range(max(len(left), len(right))):
        a = left[index] if index < len(left) else 0
        b = right[index] if index < len(right) else 0
        if a != b:
            return -1 if a < b else 1
    return 0


def encode(values: tuple[int, ...]) -> Sign:
    """Finite counterpart of concatenating +^(f(alpha)+1) followed by -."""
    if any(not isinstance(v, int) or v < 0 for v in values):
        raise ValueError("block values must be nonnegative integers")
    return tuple(sign for value in values for sign in (1,) * (value + 1) + (-1,))


def decode(word: Sign) -> tuple[int, ...]:
    values: list[int] = []
    run = 0
    for sign in word:
        if sign == 1:
            run += 1
        elif sign == -1:
            if run == 0:
                raise ValueError("a delimiter must follow a nonempty plus run")
            values.append(run - 1)
            run = 0
        else:
            raise ValueError("signs must be -1 or 1")
    if run:
        raise ValueError("the last block has no delimiter")
    return tuple(values)


def verify() -> dict[str, object]:
    cone_checks = 0
    candidates = tuple(signs(8))
    for s in signs(6):
        left = [s[:i] for i, bit in enumerate(s) if bit == 1]
        right = [s[:i] for i, bit in enumerate(s) if bit == -1]
        for x in candidates:
            separates = all(compare(a, x) < 0 for a in left) and all(
                compare(x, b) < 0 for b in right
            )
            extends = len(x) >= len(s) and x[:len(s)] == s
            check(separates == extends, f"cone identity failed: {s}, {x}")
            check(compare(s, x) == -compare(x, s), "order antisymmetry failed")
            cone_checks += 1

    block_checks = 0
    prefix_checks = 0
    for length in range(6):
        for values in itertools.product(range(4), repeat=length):
            encoded = encode(values)
            check(decode(encoded) == values, f"block round trip failed: {values}")
            block_checks += 1
            endpoints = [0]
            for value in values:
                endpoints.append(endpoints[-1] + value + 2)
            for cut in range(len(encoded)):
                count = next(i for i, endpoint in enumerate(endpoints) if endpoint >= cut)
                check(
                    encode(values[:count])[:cut] == encoded[:cut],
                    "finite proper-prefix locality failed",
                )
                prefix_checks += 1

    invalid_checks = 0
    for invalid in [(-1,), (1,), (1, -1, -1), (1, -1, 1), (0,)]:
        try:
            decode(invalid)
        except ValueError:
            invalid_checks += 1
        else:
            raise AssertionError(f"invalid encoding accepted: {invalid}")

    append_checks = 0
    binary_words = [tuple((s + 1) // 2 for s in word) for word in signs(4)]
    for slots in itertools.product((-1, 0, 1), repeat=5):
        # -1 denotes an unspecified coordinate; 0 and 1 are actual values.
        partial = {i: bit for i, bit in enumerate(slots) if bit != -1}
        old_length = max(partial, default=-1) + 1
        initial = tuple(partial.get(i, 0) for i in range(old_length))
        for target in binary_words:
            extended = initial + target
            check(all(extended[i] == bit for i, bit in partial.items()), "extension failed")
            check(extended[old_length:] == target, "target block missing")
            append_checks += 1

    coordinate_checks = 0
    indices = frozenset(range(7))
    masks = [frozenset(i for i in indices if bits & (1 << i)) for bits in range(128)]
    for f in masks:
        for h in masks:
            check((indices - f) & (indices - h) == indices - (f | h), "meet identity failed")
            check(((indices - f) <= (indices - h)) == (h <= f), "order reversal failed")
            check((tuple(sorted(f)) == tuple(sorted(h))) == (f == h), "mask recovery failed")
            coordinate_checks += 1

    return {
        "status": "PASS",
        "checks": {
            "separator_cone_pairs": cone_checks,
            "block_round_trips": block_checks,
            "proper_prefix_locality": prefix_checks,
            "invalid_encodings_rejected": invalid_checks,
            "finite_partial_condition_extensions": append_checks,
            "coordinate_mask_pairs": coordinate_checks,
        },
        "scope": "Finite sign identities, finite ordinal-block analogues, and Boolean bookkeeping.",
        "not_verified": [
            "freshness over inner models",
            "forcing or genericity",
            "infinite cofinality and cardinal preservation",
            "the successor-of-singular product input",
            "external saturation",
            "class back-and-forth or conjugacy classification",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="optional JSON results path")
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
