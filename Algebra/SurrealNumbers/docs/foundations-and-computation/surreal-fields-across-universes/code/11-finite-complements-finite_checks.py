#!/usr/bin/env python3
"""Finite regression checks for Beyond the First Omitted Cut.

These checks test sign and coding identities only. They do not test forcing,
freshness, infinite cofinalities, saturation, or proper-class constructions.
Python 3.10+, standard library only. Run from any directory.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Iterable

SignWord = tuple[int, ...]


def compare(left: SignWord, right: SignWord) -> int:
    """Lexicographic sign comparison with undefined=0, minus=-1, plus=1."""
    for i in range(max(len(left), len(right))):
        a = left[i] if i < len(left) else 0
        b = right[i] if i < len(right) else 0
        if a != b:
            return 1 if a > b else -1
    return 0


def words(alphabet: Iterable[int], maximum_length: int) -> list[tuple[int, ...]]:
    letters = tuple(alphabet)
    return [w for n in range(maximum_length + 1)
            for w in itertools.product(letters, repeat=n)]


def is_extension(root: SignWord, candidate: SignWord) -> bool:
    return len(candidate) >= len(root) and candidate[:len(root)] == root


def block_encode(values: tuple[int, ...], width: int) -> SignWord:
    if width < 2 or any(v < 0 or v >= width for v in values):
        raise ValueError("Invalid block width or alphabet value")
    return tuple(1 if position == value else -1
                 for value in values for position in range(width))


def block_decode(code: SignWord, width: int) -> tuple[int, ...]:
    if width < 2 or len(code) % width:
        raise ValueError("Code length must be a multiple of the block width")
    answer = []
    for i in range(0, len(code), width):
        block = code[i:i + width]
        if block.count(1) != 1 or any(v not in (-1, 1) for v in block):
            raise ValueError("A block must have exactly one plus")
        answer.append(block.index(1))
    return tuple(answer)


def run() -> dict[str, object]:
    signs = words((-1, 1), 7)
    counts = {"order_comparisons": 0, "cone_equivalences": 0,
              "first_disagreement_checks": 0, "block_round_trips": 0,
              "block_prefix_checks": 0, "partial_function_round_trips": 0}

    # Independent order realization by finite balanced-ternary weights.
    values = {s: sum(bit * 3 ** (7 - i) for i, bit in enumerate(s))
              for s in signs}
    assert len(set(values.values())) == len(signs)
    for s in signs:
        left = [s[:i] for i, bit in enumerate(s) if bit == 1]
        right = [s[:i] for i, bit in enumerate(s) if bit == -1]
        for t in signs:
            expected = (values[s] > values[t]) - (values[s] < values[t])
            assert compare(s, t) == expected
            counts["order_comparisons"] += 1
            separated = (all(compare(a, t) < 0 for a in left)
                         and all(compare(t, b) < 0 for b in right))
            assert separated == is_extension(s, t), (s, t)
            counts["cone_equivalences"] += 1
            if is_extension(s, t):
                continue
            # An earlier-ending candidate is allowed: undefined participates.
            d = next(i for i in range(len(s))
                     if i >= len(t) or s[i] != t[i])
            for j in range(d + 1, len(s) + 1):
                assert compare(t, s[:j]) == compare(t, s)
                counts["first_disagreement_checks"] += 1

    for width in (2, 3, 4):
        for n in range(5):
            seen: dict[SignWord, tuple[int, ...]] = {}
            prefix_outputs: dict[tuple[int, tuple[int, ...]], SignWord] = {}
            for f in itertools.product(range(width), repeat=n):
                encoded = block_encode(f, width)
                assert block_decode(encoded, width) == f
                assert encoded not in seen
                seen[encoded] = f
                counts["block_round_trips"] += 1
                for length in range(len(encoded) + 1):
                    needed = (length + width - 1) // width
                    key = (length, f[:needed])
                    prefix = encoded[:length]
                    assert prefix_outputs.setdefault(key, prefix) == prefix
                    counts["block_prefix_checks"] += 1

    # Alphabet {0,1}, blank=-1, fixed two-letter binary blocks.
    codes = {-1: (1, 0), 0: (0, 0), 1: (0, 1)}
    inverse = {value: key for key, value in codes.items()}
    recovered_conditions: dict[tuple[int, ...], tuple[int, ...]] = {}
    for n in range(7):
        for raw in itertools.product((-1, 0, 1), repeat=n):
            canonical = list(raw)
            while canonical and canonical[-1] == -1:
                canonical.pop()
            p = tuple(canonical)
            encoded = tuple(bit for symbol in p for bit in codes[symbol])
            decoded = tuple(inverse[encoded[i:i + 2]]
                            for i in range(0, len(encoded), 2))
            assert decoded == p
            assert recovered_conditions.setdefault(encoded, p) == p
            counts["partial_function_round_trips"] += 1

    return {"status": "PASS", "scope": "Finite combinatorial identities only",
            "not_verified": ["freshness", "forcing", "infinite cofinality",
                             "cardinal preservation", "saturation", "class recursion"],
            "maximum_sign_length": 7, "finite_sign_words": len(signs),
            "counts": counts, "total_checks": sum(counts.values())}


if __name__ == "__main__":
    result = run()
    output = Path(__file__).with_name("results.json")
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
