"""Exact, streaming column elimination over the two-element field."""
from __future__ import annotations

from collections.abc import Iterable
from .limits import Budget


def rank_f2(columns: Iterable[int], *, budget: Budget | None = None) -> int:
    """Column vectors are nonnegative integers, one bit per row.

    This is deterministic elimination, not randomized rank estimation.
    Neither pivot columns nor their high bits are truncated.
    """
    pivots: dict[int, int] = {}
    operations = 0
    for column in columns:
        if type(column) is not int or column < 0:
            raise ValueError("Columns must be nonnegative integer bitsets")
        while column:
            top = column.bit_length() - 1
            other = pivots.get(top)
            if other is None:
                pivots[top] = column
                break
            column ^= other
            operations += 1
            if budget is not None and operations % 1024 == 0:
                budget.check()
        if budget is not None:
            budget.check()
    return len(pivots)
