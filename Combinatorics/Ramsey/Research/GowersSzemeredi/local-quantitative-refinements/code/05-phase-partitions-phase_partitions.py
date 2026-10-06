"""Exact finite partitions for simultaneous linear phases.

All structural calculations use Fraction/integer arithmetic. A phase is given
by its slope in R/Z as a rational number. The returned progressions share one
positive common difference and partition range(n) without an exceptional set.
This module has no third-party dependencies.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import prod, isqrt
from typing import Iterable, Sequence


@dataclass(frozen=True)
class Progression:
    start: int
    step: int
    length: int

    def points(self) -> range:
        return range(self.start, self.start + self.step * self.length, self.step)


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def circle_norm(x: Fraction) -> Fraction:
    y = x % 1
    return min(y, 1 - y)


def arc_width(points: Iterable[Fraction]) -> Fraction:
    """Length of the shortest closed circular arc containing a finite set."""
    p = sorted(set(x % 1 for x in points))
    if len(p) < 2:
        return Fraction(0)
    largest_gap = max([p[i + 1] - p[i] for i in range(len(p) - 1)]
                      + [1 + p[0] - p[-1]])
    return 1 - largest_gap


def chunk_residues(n: int, q: int, lower: int) -> list[Progression]:
    if n < 1 or lower < 1 or q < 1 or q * lower > n:
        raise ValueError("Require n, q, lower >= 1 and q*lower <= n.")
    result = []
    for residue in range(q):
        size = (n - 1 - residue) // q + 1
        blocks, remainder = divmod(size, lower)
        for k in range(blocks - 1):
            result.append(Progression(residue + k * lower * q, q, lower))
        result.append(Progression(residue + (blocks - 1) * lower * q,
                                  q, lower + remainder))
    return result


def single_scale(n: int, epsilon: Fraction) -> int:
    """Largest L satisfying 2 L(L-1) <= epsilon*n, without square roots."""
    if n < 1 or not 0 < epsilon <= 1:
        raise ValueError("Require n >= 1 and 0 < epsilon <= 1.")
    low, high = 1, n
    while low < high:
        mid = (low + high + 1) // 2
        if 2 * mid * (mid - 1) <= epsilon * n:
            low = mid
        else:
            high = mid - 1
    return low


def single_partition(n: int, slope: Fraction, epsilon: Fraction
                     ) -> tuple[int, list[Progression]]:
    lower = single_scale(n, epsilon)
    if lower == 1:
        return lower, chunk_residues(n, 1, 1)
    Q = n // lower
    q = next((q for q in range(1, Q + 1)
              if circle_norm(q * slope) <= Fraction(1, Q + 1)), None)
    if q is None:
        raise ArithmeticError("Circular pigeonhole invariant failed.")
    return lower, chunk_residues(n, q, lower)


def box_counts(lower: int, widths: Sequence[Fraction]) -> list[int]:
    return [max(1, ceil_fraction(Fraction(2 * (lower - 1)) / e)) for e in widths]


def simultaneous_scale(n: int, widths: Sequence[Fraction]) -> int:
    if n < 1 or not widths or any(not 0 < e <= 1 for e in widths):
        raise ValueError("Require n >= 1, at least one width, and widths in (0,1].")
    low, high = 1, n
    while low < high:
        mid = (low + high + 1) // 2
        if mid * prod(box_counts(mid, widths)) <= n:
            low = mid
        else:
            high = mid - 1
    return low


def simultaneous_partition(n: int, slopes: Sequence[Fraction],
                           widths: Sequence[Fraction]
                           ) -> tuple[int, list[Progression]]:
    if len(slopes) != len(widths):
        raise ValueError("The slope and width lists must have the same length.")
    lower = simultaneous_scale(n, widths)
    if lower == 1:
        return lower, chunk_residues(n, 1, 1)
    counts = box_counts(lower, widths)
    boxes = prod(counts)
    seen: dict[tuple[int, ...], int] = {}
    q = None
    for k in range(boxes + 1):
        cell = tuple(int(((k * a) % 1) * Q) for a, Q in zip(slopes, counts))
        if cell in seen:
            q = k - seen[cell]
            break
        seen[cell] = k
    if q is None:
        raise ArithmeticError("Rectangular pigeonhole invariant failed.")
    return lower, chunk_residues(n, q, lower)


def check_partition(n: int, lower: int, cells: Sequence[Progression],
                    slopes: Sequence[Fraction], widths: Sequence[Fraction]) -> None:
    """Independent exact checks; raises AssertionError on failure."""
    assert cells and len(slopes) == len(widths)
    assert len({p.step for p in cells}) == 1
    all_points = [x for p in cells for x in p.points()]
    assert sorted(all_points) == list(range(n))
    assert len(cells) * lower <= n
    for p in cells:
        assert p.step > 0 and lower <= p.length <= 2 * lower - 1
        assert all(0 <= x < n for x in p.points())
        for slope, width in zip(slopes, widths):
            assert arc_width(slope * x for x in p.points()) <= width


def water_fill(weights: Sequence[Fraction], budget: Fraction,
               cap: Fraction = Fraction(1, 4)) -> list[Fraction]:
    """Maximize product(widths) under sum(weight*width)<=budget and width<=cap.

    This optimizes the continuous lower-bound surrogate, not the discontinuous
    integer ceiling formula. Inputs and output are exact rational numbers.
    """
    if not weights or any(w <= 0 for w in weights) or budget <= 0 or not 0 < cap <= 1:
        raise ValueError("Require positive weights/budget and cap in (0,1].")
    if budget >= sum(w * cap for w in weights):
        return [cap] * len(weights)
    remaining = set(range(len(weights)))
    widths = [Fraction(0)] * len(weights)
    residual = budget
    while remaining:
        level = residual / len(remaining)
        saturated = {i for i in remaining if weights[i] * cap <= level}
        if not saturated:
            for i in remaining:
                widths[i] = level / weights[i]
            break
        for i in saturated:
            widths[i] = cap
            residual -= weights[i] * cap
        remaining -= saturated
    return widths


def capped_partition(n: int, slope: Fraction, epsilon: Fraction
                     ) -> tuple[int, list[Progression]]:
    """Sharp 1/3 theorem: sqrt(epsilon*n)/3 <= size <= sqrt(epsilon*n).

    Requires epsilon*n >= 1. The 1/3 coefficient is the optimal uniform
    coefficient when the upper coefficient is fixed at 1.
    """
    if n < 1 or not 0 < epsilon <= 1 or epsilon*n < 1:
        raise ValueError("Require n >= 1, 0 < epsilon <= 1, epsilon*n >= 1.")
    t = epsilon*n
    upper = isqrt(t.numerator // t.denominator)
    lower = (upper + 1) // 2
    if lower == 1:
        cells = chunk_residues(n, 1, 1)
    else:
        Q = n // lower
        q = next(q for q in range(1, Q+1)
                 if circle_norm(q*slope) <= Fraction(1, Q+1))
        cells = chunk_residues(n, q, lower)
    assert all(9*p.length*p.length >= t and p.length*p.length <= t for p in cells)
    return lower, cells
