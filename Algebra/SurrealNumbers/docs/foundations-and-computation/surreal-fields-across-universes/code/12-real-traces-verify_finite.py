#!/usr/bin/env python3
"""Exact finite checks for 'Beyond Gap Spectra'.

These are regression checks for local combinatorial identities, NOT proofs of
freshness, forcing, saturation, cofinality, or any proper-class theorem.
Only Python's standard library is required.
"""
from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable

Sign = tuple[int, ...]


def words(alphabet: Iterable[int], max_length: int) -> Iterable[tuple[int, ...]]:
    alphabet = tuple(alphabet)
    for length in range(max_length + 1):
        yield from itertools.product(alphabet, repeat=length)


def compare_signs(s: Sign, t: Sign) -> int:
    """Lexicographic comparison with termination strictly between -1 and +1."""
    for a, b in itertools.zip_longest(s, t, fillvalue=0):
        if a != b:
            return 1 if a > b else -1
    return 0


def finite_surreal_value(s: Sign) -> Fraction:
    """An independent exact dyadic evaluation of a finite surreal sign."""
    if not s:
        return Fraction(0)
    run = 1
    while run < len(s) and s[run] == s[0]:
        run += 1
    value = Fraction(s[0] * run)
    for index in range(run, len(s)):
        value += Fraction(s[index], 2 ** (index - run + 1))
    return value


def check_signs() -> dict[str, int]:
    signs = tuple(words((-1, 1), 7))
    values = {s: finite_surreal_value(s) for s in signs}
    assert len(set(values.values())) == len(signs)
    comparisons = separators = 0
    for s in signs:
        left = tuple(s[:i] for i, digit in enumerate(s) if digit == 1)
        right = tuple(s[:i] for i, digit in enumerate(s) if digit == -1)
        for t in signs:
            expected = (values[s] > values[t]) - (values[s] < values[t])
            assert compare_signs(s, t) == expected, (s, t)
            comparisons += 1
            in_interval = all(compare_signs(a, t) < 0 for a in left) and all(
                compare_signs(t, b) < 0 for b in right
            )
            extends = len(t) >= len(s) and t[:len(s)] == s
            assert in_interval == extends, (s, t, in_interval, extends)
            separators += 1
    return {
        "maximum_sign_length": 7,
        "signs": len(signs),
        "exact_dyadic_order_comparisons": comparisons,
        "prefix_separator_pairs": separators,
    }


def block_encode(word: tuple[int, ...], width: int) -> Sign:
    if width < 1 or any(not 0 <= digit < width for digit in word):
        raise ValueError("Digits must lie in the nonempty block alphabet.")
    return tuple(1 if position == digit else -1
                 for digit in word for position in range(width))


def block_decode(code: Sign, width: int) -> tuple[int, ...]:
    if width < 1 or len(code) % width:
        raise ValueError("The code must consist of complete nonempty blocks.")
    result = []
    for start in range(0, len(code), width):
        block = code[start:start + width]
        if block.count(1) != 1 or any(d not in (-1, 1) for d in block):
            raise ValueError("Every block must have exactly one plus sign.")
        result.append(block.index(1))
    return tuple(result)


def check_blocks() -> dict[str, int]:
    round_trips = prefixes = 0
    for width in range(2, 6):
        for word in words(range(width), 5):
            code = block_encode(word, width)
            assert block_decode(code, width) == word
            round_trips += 1
            for length in range(len(code) + 1):
                needed = (length + width - 1) // width
                assert block_encode(word[:needed], width)[:length] == code[:length]
                prefixes += 1
    return {"width_min": 2, "width_max": 5, "maximum_word_length": 5,
            "round_trips": round_trips, "prefix_dependencies": prefixes}


def ternary_encode(word: tuple[int, ...]) -> Fraction:
    return sum((Fraction(2 * digit, 3 ** (i + 1))
                for i, digit in enumerate(word)), Fraction(0))


def ternary_decode(value: Fraction, length: int) -> tuple[int, ...]:
    result = []
    for _ in range(length):
        value *= 3
        digit = 1 if value >= 2 else 0
        if digit:
            value -= 2
        assert 0 <= value <= 1
        result.append(digit)
    return tuple(result)


def check_ternary() -> dict[str, int]:
    checked = 0
    for length in range(11):
        seen: set[Fraction] = set()
        for word in itertools.product((0, 1), repeat=length):
            value = ternary_encode(word)
            assert value not in seen
            seen.add(value)
            assert ternary_decode(value, length) == word
            checked += 1
    return {"maximum_length": 10, "exact_round_trips": checked,
            "fixed_length_injectivity_checks": 11}


def partial_orders(n: int) -> Iterable[set[tuple[int, int]]]:
    """All labelled partial orders, with no isomorphism reduction."""
    pairs = tuple(itertools.combinations(range(n), 2))
    for states in itertools.product((0, 1, 2), repeat=len(pairs)):
        relation = {(i, i) for i in range(n)}
        for (i, j), state in zip(pairs, states):
            if state == 1:
                relation.add((i, j))
            elif state == 2:
                relation.add((j, i))
        if all((i, k) in relation
               for i, j in relation for j2, k in relation if j == j2):
            yield relation


def check_downsets() -> dict[str, object]:
    counts: dict[int, int] = {}
    pair_checks = 0
    for n in range(5):
        counts[n] = 0
        for relation in partial_orders(n):
            counts[n] += 1
            down = [{q for q in range(n) if (q, p) in relation}
                    for p in range(n)]
            for p in range(n):
                for q in range(n):
                    assert ((p, q) in relation) == (down[p] <= down[q])
                    pair_checks += 1
    assert counts == {0: 1, 1: 1, 2: 3, 3: 19, 4: 219}
    return {"labelled_partial_order_counts": counts, "pair_checks": pair_checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    results = {
        "status": "PASS",
        "scope": "Finite local identities only; no forcing or infinitary theorem is verified.",
        "signs": check_signs(),
        "block_codes": check_blocks(),
        "ternary_codes": check_ternary(),
        "principal_downsets": check_downsets(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
