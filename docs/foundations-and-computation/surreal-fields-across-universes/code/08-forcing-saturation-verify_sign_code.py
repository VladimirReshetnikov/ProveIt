#!/usr/bin/env python3
"""Finite checks for the sign-code lemmas; not a proof of transfinite results.

Run with Python 3.10 or later. No external packages or network access required.
All tests are deterministic and bounded. Change the constants in main() to
increase the search, noting that the number of sign strings is exponential.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import product

Sign = tuple[int, ...]


def sign_compare(left: Sign, right: Sign) -> int:
    """First disagreement order, with a missing sign represented by zero."""
    for j in range(max(len(left), len(right))):
        a = left[j] if j < len(left) else 0
        b = right[j] if j < len(right) else 0
        if a != b:
            return (a > b) - (a < b)
    return 0


def is_prefix(prefix: Sign, sequence: Sign) -> bool:
    return len(prefix) <= len(sequence) and sequence[:len(prefix)] == prefix


def dyadic_value(sequence: Sign) -> Fraction:
    """Independent finite sign evaluation: initial integer run, then halves."""
    if not sequence:
        return Fraction(0)
    if any(sign not in (-1, 1) for sign in sequence):
        raise ValueError("A sign must be -1 or +1.")
    initial = sequence[0]
    k = 0
    while k < len(sequence) and sequence[k] == initial:
        k += 1
    value = Fraction(initial * k)
    for offset, sign in enumerate(sequence[k:], start=1):
        value += Fraction(sign, 2 ** offset)
    return value


def sign_strings(max_length: int) -> list[Sign]:
    if max_length < 0:
        raise ValueError("The length bound must be nonnegative.")
    return [s for n in range(max_length + 1) for s in product((-1, 1), repeat=n)]


def encode(values: tuple[int, ...]) -> tuple[Sign, list[tuple[Sign, Sign]]]:
    """Return C(f) and the pairs (lower endpoint, upper endpoint)."""
    prefix: Sign = ()
    endpoints: list[tuple[Sign, Sign]] = []
    for value in values:
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError("Finite ordinal entries must be nonnegative integers.")
        upper = prefix + (1,) * value
        lower = upper + (-1,)
        endpoints.append((lower, upper))
        prefix = lower + (1,)
    return prefix, endpoints


def decode(sequence: Sign) -> tuple[int, ...]:
    """Parse complete finite blocks +^n,-,+, rejecting malformed inputs."""
    entries: list[int] = []
    index = 0
    while index < len(sequence):
        start = index
        while index < len(sequence) and sequence[index] == 1:
            index += 1
        value = index - start
        if index >= len(sequence) or sequence[index] != -1:
            raise ValueError("A complete block needs a minus marker.")
        index += 1
        if index >= len(sequence) or sequence[index] != 1:
            raise ValueError("A minus marker must be followed by one plus marker.")
        index += 1
        entries.append(value)
    return tuple(entries)


class Checker:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def check(self, category: str, statement: bool, detail: object = None) -> None:
        self.counts[category] += 1
        if not statement:
            raise AssertionError(f"{category} failed: {detail!r}")


def main() -> None:
    checker = Checker()
    comparison_bound = 7
    prefix_bound = 5
    interval_point_bound = 9
    block_count_bound = 3
    entry_bound = 3
    code_point_bound = 10

    comparison_points = sign_strings(comparison_bound)
    values = {s: dyadic_value(s) for s in comparison_points}
    for a in comparison_points:
        for b in comparison_points:
            rational_order = (values[a] > values[b]) - (values[a] < values[b])
            checker.check("sign order versus dyadic values",
                          sign_compare(a, b) == rational_order, (a, b))

    prefixes = sign_strings(prefix_bound)
    interval_points = sign_strings(interval_point_bound)
    for u in prefixes:
        lower = u + (-1,)
        forced_prefix = lower + (1,)
        for y in interval_points:
            inside = sign_compare(lower, y) < 0 and sign_compare(y, u) < 0
            checker.check("two-bound cone identity", inside == is_prefix(forced_prefix, y),
                          (u, y))

    code_points = sign_strings(code_point_bound)
    code_count = 0
    for n in range(1, block_count_bound + 1):
        for entries in product(range(entry_bound + 1), repeat=n):
            code_count += 1
            code, endpoints = encode(entries)
            checker.check("finite decoding", decode(code) == entries, entries)
            for lower, upper in endpoints:
                checker.check("code between endpoints",
                              sign_compare(lower, code) < 0 < sign_compare(upper, code), entries)
            for j in range(len(endpoints)):
                for k in range(j + 1, len(endpoints)):
                    lj, uj = endpoints[j]
                    lk, uk = endpoints[k]
                    checker.check("strict nesting", sign_compare(lj, lk) < 0
                                  and sign_compare(uk, uj) < 0, entries)
            extra = [code[:k] for k in range(len(code) + 1)]
            extra += [code + tail for length in range(1, 4)
                      for tail in product((-1, 1), repeat=length)]
            for y in code_points + extra:
                inside_all = all(sign_compare(lower, y) < 0 < sign_compare(upper, y)
                                 for lower, upper in endpoints)
                checker.check("finite intersection equals final cone",
                              inside_all == is_prefix(code, y), (entries, y))

    print("Finite sign-code verification: PASS")
    print("Scope: finite sign order only; no transfinite or formal-proof claim.")
    print(f"Comparison strings: all lengths 0..{comparison_bound} ({len(comparison_points)} strings)")
    print(f"Cone prefixes: all lengths 0..{prefix_bound} ({len(prefixes)} prefixes)")
    print(f"Cone test points: all lengths 0..{interval_point_bound} ({len(interval_points)} points)")
    print(f"Block lists: lengths 1..{block_count_bound}, entries 0..{entry_bound} ({code_count} lists)")
    print(f"Code test points: all lengths 0..{code_point_bound}, plus code prefixes and short tails")
    for category, count in checker.counts.items():
        print(f"{category}: {count:,} checks")
    print(f"Total: {sum(checker.counts.values()):,} checks")


if __name__ == "__main__":
    main()
