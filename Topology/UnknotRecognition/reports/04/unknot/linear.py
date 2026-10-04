"""Exact linear algebra over F_2 using nonnegative integers as bit vectors."""
from __future__ import annotations

from collections.abc import Callable, Iterable


def set_bits(value: int):
    """Yield the positions of the nonzero bits, in increasing order."""
    if type(value) is not int or value < 0:
        raise ValueError("bit vector must be a nonnegative integer")
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def rank_f2(columns: Iterable[int], rows: int,
            tick: Callable[[], None] | None = None) -> int:
    if type(rows) is not int or rows < 0:
        raise ValueError("rows must be a nonnegative integer")
    pivots: dict[int, int] = {}
    for column in columns:
        if type(column) is not int or column < 0 or column.bit_length() > rows:
            raise ValueError("invalid F2 column")
        if tick:
            tick()
        while column:
            leading = column.bit_length() - 1
            pivot = pivots.get(leading)
            if pivot is None:
                pivots[leading] = column
                break
            column ^= pivot
            if tick:
                tick()
    return len(pivots)


def apply_matrix(columns: list[int] | tuple[int, ...], vector: int) -> int:
    if type(vector) is not int or vector < 0 or vector.bit_length() > len(columns):
        raise ValueError("vector has the wrong dimension")
    result = 0
    for position in set_bits(vector):
        result ^= columns[position]
    return result
