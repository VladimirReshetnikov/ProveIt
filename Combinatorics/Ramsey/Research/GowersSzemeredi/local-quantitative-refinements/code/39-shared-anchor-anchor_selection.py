#!/usr/bin/env python3
"""Exact shared-anchor selection for finite families of disjoint classes.

No third-party dependencies.  All certificate computations use Fraction.
A target is recovered if it is sampled itself, or its class contains at
least `threshold` distinct sampled columns.  Class labels need not agree
between rows.  The ambient column set is range(m).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb, isqrt
from typing import Iterable, Sequence


def choose(n: int, k: int) -> int:
    """Binomial coefficient, with the zero convention outside 0 <= k <= n."""
    return comb(n, k) if n >= 0 and 0 <= k <= n else 0


def _parameters(m: int, r: int, threshold: int) -> None:
    if not isinstance(m, int) or m < 1:
        raise ValueError("m must be a positive integer")
    if not isinstance(r, int) or not 0 <= r <= m:
        raise ValueError("r must be an integer in [0,m]")
    if not isinstance(threshold, int) or threshold < 1:
        raise ValueError("threshold must be a positive integer")


def class_loss(m: int, r: int, threshold: int, size: int) -> Fraction:
    """Expected discarded mass of ONE class, normalized by the ambient m."""
    _parameters(m, r, threshold)
    if not isinstance(size, int) or not 0 <= size <= m:
        raise ValueError("class size must lie in [0,m]")
    numerator = sum(
        (size-j) * choose(size, j) * choose(m-size, r-j)
        for j in range(min(threshold-1, r, size)+1)
    )
    return Fraction(numerator, m * choose(m, r))


def low_occupancy_identity(m: int, r: int, threshold: int,
                           size: int) -> Fraction:
    """Independent (r+1)-subset double-counting expression for class_loss."""
    _parameters(m, r, threshold)
    if not 0 <= size <= m:
        raise ValueError("invalid size")
    if r == m:
        return Fraction(0)
    numerator = sum(
        j * choose(size, j) * choose(m-size, r+1-j)
        for j in range(1, min(threshold, size, r+1)+1)
    )
    return Fraction(numerator, m * choose(m, r))


def universal_bound(m: int, r: int, threshold: int,
                    mean_classes: Fraction | int) -> Fraction:
    _parameters(m, r, threshold)
    if mean_classes < 0:
        raise ValueError("mean_classes must be nonnegative")
    return min(Fraction(1), Fraction(mean_classes) * threshold * (m-r)
               / (m * (r+1)))


def minimax_profile(m: int, q: int, r: int,
                    threshold: int) -> tuple[Fraction, tuple[int, ...]]:
    """Exact finite minimax value and a maximizing size profile.

    Dynamic program maximizes sum(class_loss(s_i)) over q nonnegative
    sizes with total <= m.  Time O(q*m^2), memory O(q*m) including parents.
    """
    _parameters(m, r, threshold)
    if not isinstance(q, int) or q < 0:
        raise ValueError("q must be a nonnegative integer")
    losses = [class_loss(m, r, threshold, s) for s in range(m+1)]
    dp = [Fraction(0) for _ in range(m+1)]
    parents: list[list[int]] = []
    for _ in range(q):
        new: list[Fraction] = []
        picked: list[int] = []
        for budget in range(m+1):
            value, size = max((dp[budget-s]+losses[s], s)
                              for s in range(budget+1))
            new.append(value)
            picked.append(size)
        dp = new
        parents.append(picked)
    sizes: list[int] = []
    budget = m
    for picked in reversed(parents):
        size = picked[budget]
        sizes.append(size)
        budget -= size
    return dp[m], tuple(reversed(sizes))


def first_mode(m: int, r: int, threshold: int) -> int:
    """Least class size maximizing one-class loss (exact; O(m) values)."""
    _parameters(m, r, threshold)
    losses = [class_loss(m, r, threshold, s) for s in range(m + 1)]
    return losses.index(max(losses))


def affine_first_mode(m: int, r: int) -> int:
    """Closed-form affine first mode, computed by integer square root.

    For 2 <= r < m, the cap is ceil((B + sqrt(D))/(2*A)), with
    A=r*r-1, B=(r-2)*m+2*r-1, D=B*B+4*A*(m-r)*(m-r+1).
    There are no floating-point comparisons near integer roots.
    """
    _parameters(m, r, 2)
    if r == m:
        return 0
    if r < 2:
        return m
    a = r*r - 1
    b = (r-2)*m + 2*r - 1
    c = (m-r)*(m-r+1)
    k = (b + isqrt(b*b + 4*a*c)) // (2*a)
    return k if a*k*k-b*k-c == 0 else k+1


def balanced_minimax_profile(m: int, q: int, r: int,
                             threshold: int) -> tuple[Fraction, tuple[int, ...]]:
    """Exact closed profile formula; independent of the dynamic program.

    Balance the used column budget min(m,q*cap) among q classes.  The
    affine cap uses an explicit quadratic root with integer arithmetic.
    For general threshold the cap is found by scanning m+1 marginal values.
    """
    _parameters(m, r, threshold)
    if not isinstance(q, int) or q < 0:
        raise ValueError("q must be a nonnegative integer")
    if q == 0:
        return Fraction(0), ()
    cap = affine_first_mode(m, r) if threshold == 2 else first_mode(m, r, threshold)
    used = min(m, q*cap)
    low, remainder = divmod(used, q)
    high = (used+q-1)//q
    value = ((q-remainder)*class_loss(m, r, threshold, low)
             + remainder*class_loss(m, r, threshold, high))
    return value, (low,)*(q-remainder) + (high,)*remainder


@dataclass(frozen=True)
class Row:
    classes: tuple[frozenset[int], ...]
    weight: Fraction = Fraction(1)

    @staticmethod
    def make(classes: Iterable[Iterable[int]], weight: Fraction | int = 1) -> 'Row':
        return Row(tuple(frozenset(c) for c in classes), Fraction(weight))


def validate_rows(m: int, rows: Sequence[Row]) -> Fraction:
    if m < 1 or not rows:
        raise ValueError("positive m and at least one row are required")
    total = Fraction(0)
    for row in rows:
        if row.weight < 0:
            raise ValueError("row weights must be nonnegative")
        seen: set[int] = set()
        for cls in row.classes:
            if any(not isinstance(x, int) or not 0 <= x < m for x in cls):
                raise ValueError("class member is not a column in range(m)")
            if seen.intersection(cls):
                raise ValueError("classes in a row must be disjoint")
            seen.update(cls)
        total += row.weight
    if total == 0:
        raise ValueError("at least one row must have positive weight")
    return total


def discarded_mass(m: int, rows: Sequence[Row], anchors: Iterable[int],
                    threshold: int) -> Fraction:
    total = validate_rows(m, rows)
    selected = frozenset(anchors)
    _parameters(m, len(selected), threshold)
    if not selected.issubset(range(m)):
        raise ValueError("anchor outside column set")
    mass = sum((row.weight * sum(
        len(cls-selected) if len(cls & selected) < threshold else 0
        for cls in row.classes) for row in rows), Fraction(0))
    return mass / (m * total)


def conditional_mass(m: int, rows: Sequence[Row], selected: frozenset[int],
                     r: int, threshold: int) -> Fraction:
    """Expected final loss, conditioned on selected being in an r-subset."""
    total = validate_rows(m, rows)
    _parameters(m, r, threshold)
    if len(selected) > r or not selected.issubset(range(m)):
        raise ValueError("invalid partial anchor set")
    remaining = m - len(selected)
    draws = r - len(selected)
    denominator = choose(remaining, draws)
    numerator = Fraction(0)
    for row in rows:
        for cls in row.classes:
            hits = len(cls & selected)
            if hits >= threshold:
                continue
            available = len(cls)-hits
            value = sum(
                (available-j) * choose(available, j)
                * choose(remaining-available, draws-j)
                for j in range(min(threshold-hits-1, available, draws)+1)
            )
            numerator += row.weight * value
    return numerator / (denominator * m * total)


def select_anchors(m: int, rows: Sequence[Row], r: int,
                   threshold: int) -> tuple[tuple[int, ...], tuple[Fraction, ...]]:
    """Derandomize uniform r-subset sampling by conditional expectations.

    Returns anchors and a monotonically nonincreasing exact potential trace.
    This is an explicit finite-data algorithm, not an efficient implementation
    of the complete Szemeredi argument.
    """
    validate_rows(m, rows)
    _parameters(m, r, threshold)
    selected: frozenset[int] = frozenset()
    trace = [conditional_mass(m, rows, selected, r, threshold)]
    for _ in range(r):
        best, column = min(
            (conditional_mass(m, rows, selected | {x}, r, threshold), x)
            for x in range(m) if x not in selected
        )
        if best > trace[-1]:
            raise ArithmeticError("conditional-expectation invariant failed")
        selected |= {column}
        trace.append(best)
    actual = discarded_mass(m, rows, selected, threshold)
    if actual != trace[-1]:
        raise ArithmeticError("terminal potential does not equal actual loss")
    return tuple(sorted(selected)), tuple(trace)


def exact_average(m: int, rows: Sequence[Row], r: int,
                  threshold: int) -> Fraction:
    """Enumeration reference implementation; intended only for small m."""
    return sum((discarded_mass(m, rows, a, threshold)
                for a in combinations(range(m), r)), Fraction(0)) / choose(m, r)


if __name__ == '__main__':
    example = [Row.make([{0, 1, 2}, {5, 7}], 2),
               Row.make([{1, 3, 5, 7}, {0, 6}], 1),
               Row.make([{2}, {0, 4, 6}], 3)]
    anchors, trace = select_anchors(8, example, 3, 2)
    print('anchors:', anchors)
    print('exact loss trace:', [str(x) for x in trace])
    print('final discarded mass:', trace[-1])
