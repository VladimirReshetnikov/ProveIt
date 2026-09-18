"""Exact rank over F_2 and fraction-free integer determinants."""
from __future__ import annotations

from collections.abc import Iterable


def rank_f2(columns: Iterable[int]) -> int:
    """Column vectors are nonnegative integers whose bits are row entries."""
    pivots: dict[int, int] = {}
    for column in columns:
        if type(column) is not int or column < 0:
            raise ValueError("F2 column must be a nonnegative integer bit vector")
        while column:
            leading = column.bit_length() - 1
            pivot = pivots.get(leading)
            if pivot is None:
                pivots[leading] = column
                break
            column ^= pivot
    return len(pivots)


def determinant_bareiss(matrix: list[list[int]]) -> int:
    """Exact determinant, with row pivoting. The empty determinant is 1."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Determinant requires a square matrix")
    if any(type(x) is not int for row in matrix for x in row):
        raise ValueError("Integer entries required")
    if n == 0:
        return 1
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(n - 1):
        pivot_row = next((r for r in range(k, n) if a[r][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * a[i][j] - a[i][k] * a[k][j]
                quotient, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError("Non-exact Bareiss division")
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]
