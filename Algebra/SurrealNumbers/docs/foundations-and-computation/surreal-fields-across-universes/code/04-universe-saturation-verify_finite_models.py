#!/usr/bin/env python3
"""Finite exact-arithmetic checks for the accompanying research manuscript.

These checks concern finite sign strings and finite natural ordinal labels.
They do not verify transfinite recursion, forcing, saturation, or novelty.
Uses only the Python standard library; run with Python 3.10 or later.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product

Interval = tuple[F, F]
SignString = tuple[int, ...]


def child(interval: Interval, alpha: int) -> Interval:
    if alpha < 0:
        raise ValueError("The label must be a nonnegative integer.")
    a, b = interval
    if not a < b:
        raise ValueError("The interval must be nonempty.")
    d = b - a
    return a + d / (2 * alpha + 3), a + d / (2 * alpha + 2)


def interval_of(labels: tuple[int, ...]) -> Interval:
    interval = (F(0), F(1))
    for alpha in labels:
        interval = child(interval, alpha)
    return interval


def finite_formula(labels: tuple[int, ...]) -> Interval:
    left, length = F(0), F(1)
    for alpha in labels:
        left += length / (2 * alpha + 3)
        length /= (2 * alpha + 2) * (2 * alpha + 3)
    return left, left + length


def sign_compare(x: SignString, y: SignString) -> int:
    """Numerical comparison: -1 < undefined (0) < +1."""
    for n in range(max(len(x), len(y))):
        a = x[n] if n < len(x) else 0
        b = y[n] if n < len(y) else 0
        if a != b:
            return 1 if a > b else -1
    return 0


def main() -> None:
    checked_nodes = 0
    checked_child_pairs = 0
    checked_decodings = 0
    label_set = (0, 1, 2, 3)
    for length in range(6):
        for labels in product(label_set, repeat=length):
            interval = interval_of(labels)
            assert interval == finite_formula(labels)
            checked_nodes += 1
            a, b = interval
            test_labels = (0, 1, 2, 3, 10, 100)
            intervals = [child(interval, alpha) for alpha in test_labels]
            for ca, cb in intervals:
                assert a < ca < cb < b
            for i in range(len(intervals)):
                for j in range(i + 1, len(intervals)):
                    assert intervals[j][1] < intervals[i][0]
                    checked_child_pairs += 1
            if length:
                point = (a + b) / 2
                prefix = (F(0), F(1))
                recovered = []
                for _ in labels:
                    matches = [alpha for alpha in label_set
                               if child(prefix, alpha)[0] < point
                               < child(prefix, alpha)[1]]
                    assert len(matches) == 1
                    alpha = matches[0]
                    recovered.append(alpha)
                    prefix = child(prefix, alpha)
                assert tuple(recovered) == labels
                checked_decodings += 1

    sign_strings = [s for length in range(8)
                    for s in product((-1, 1), repeat=length)]
    checked_sign_pairs = 0
    for branch in sign_strings:
        for candidate in sign_strings:
            satisfies = all(sign_compare(candidate, branch[:n]) == sign
                            for n, sign in enumerate(branch))
            extends = (len(candidate) >= len(branch)
                       and candidate[:len(branch)] == branch)
            assert satisfies == extends
            checked_sign_pairs += 1

    print("All finite exact-arithmetic checks passed.")
    print(f"Finite interval nodes / closed-form comparisons: {checked_nodes}")
    print(f"Separated child pairs checked: {checked_child_pairs}")
    print(f"Finite branch decodings checked: {checked_decodings}")
    print(f"Canonical-cut / prefix comparisons checked: {checked_sign_pairs}")
    print("Scope: finite natural labels and finite sign strings only.")
    print("Not a formal verification of the infinite theorems or novelty.")


if __name__ == "__main__":
    main()
