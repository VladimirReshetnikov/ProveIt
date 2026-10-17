#!/usr/bin/env python3
"""Independent audit of the two-exception H/W name-map construction.

No imports from the proposal implementation. Checks the hole-routing swap,
its shortened word, contraction repair, and finite downshift by literal
iteration. This is finite supporting evidence, not a universal proof or TM.
"""
from itertools import combinations
import json


def h(x):
    return 2 if x == 0 else 0 if x == 1 else x


def w(x):
    return 1 if x == 0 else -1 if x == 1 else x - 1


def h_at(j, x):
    return h(x - j) + j


def swap_literal(lo, hi, i, x):
    assert lo <= i < hi
    x += 1
    for j in range(lo, i + 2):
        x = h_at(j, x)
    for j in (i, i + 1):
        x = h_at(j, x)
    for j in range(i + 2, hi + 1):
        x = h_at(j, x)
    return x


def shift(n):
    return "u" * n if n >= 0 else "d" * -n


def short_swap_word(lo, hi, i):
    return (shift(1 - lo) + "h" + "dh" * (i + 1 - lo)
            + "uh" + "dh" * (hi - i) + shift(hi))


def run(word, x):
    for op in word:
        x = x + 1 if op == "u" else x - 1 if op == "d" else h(x) if op == "h" else w(x)
    return x


def down_word(support):
    if not support:
        return ""
    a = max(0, 1 - min(support))
    q = max(0, max(support))
    return "u" * a + "w" * (a + q) + "u" * q


def verify():
    counts = {"protected_swaps": 0, "protected_swap_values": 0,
              "collapse_supports": 0, "collapse_values": 0,
              "downshift_supports": 0, "downshift_values": 0,
              "main_orbit_values": 0, "H_WU_identities": 0}
    for x in range(-1000, 1001):
        assert w(x) + 1 == h(x)
        counts["H_WU_identities"] += 1
    for x in range(1, 101):
        actual = x
        for b in range(201):
            if b >= x:
                assert actual == x - b - 1
                counts["main_orbit_values"] += 1
            actual = w(actual)
    for lo in range(-8, 9):
        for hi in range(lo + 1, lo + 10):
            for i in range(lo, hi):
                word = short_swap_word(lo, hi, i)
                assert len(word) == abs(1 - lo) + abs(hi) + 2 * (hi - lo) + 5
                for x in range(lo, hi + 1):
                    expected = i + 1 if x == i else i if x == i + 1 else x
                    assert swap_literal(lo, hi, i, x) == expected
                    assert run(word, x) == expected
                    counts["protected_swap_values"] += 1
                counts["protected_swaps"] += 1
    for size in range(6):
        for chosen in combinations(range(-7, 8), size):
            support = set(chosen)
            word = down_word(support)
            image = {h(x) for x in support}
            lo, hi = min(image | {0, 1}), max(image | {0, 1})
            for x in support:
                assert run(word, x) == x - 1
                assert swap_literal(lo, hi, 0, h(x)) == (2 if x == 0 else x)
                counts["downshift_values"] += 1
                counts["collapse_values"] += 1
            counts["downshift_supports"] += 1
            counts["collapse_supports"] += 1
    return {"status": "pass", "scope": "finite name-map checks only", **counts}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
