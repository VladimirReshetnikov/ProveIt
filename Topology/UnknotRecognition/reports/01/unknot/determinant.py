"""Exact knot determinant from the t=-1 Wirtinger/Fox coloring matrix.

The value 1 is INCONCLUSIVE. No floating-point determinants are used.
"""
from __future__ import annotations
from .grid import Grid


def bareiss(matrix: list[list[int]]) -> int:
    """Integer determinant with fraction-free Gaussian elimination and pivoting."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("matrix must be square")
    if any(type(x) is not int for row in matrix for x in row):
        raise ValueError("matrix entries must be integers")
    if not n:
        return 1
    a = [row[:] for row in matrix]
    sign, denominator = 1, 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot_row = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot_row is None:
                return 0
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot - a[i][k] * a[k][j]
                value, remainder = divmod(numerator, denominator)
                if remainder:
                    raise ArithmeticError("non-exact Bareiss division")
                a[i][j] = value
            a[i][k] = 0
        denominator = pivot
    return sign * a[-1][-1]


def coloring_matrix(grid: Grid) -> list[list[int]]:
    events = grid.events()
    under = [crossing for crossing, over in events if not over]
    m = len(under)
    if not m:
        return []
    under_index = {crossing: i for i, crossing in enumerate(under)}
    if len(under_index) != m or len(events) != 2 * m:
        raise ArithmeticError("inconsistent crossing traversal")
    over_arc = {}
    current = m - 1
    for crossing, over in events:
        if over:
            over_arc[crossing] = current
        else:
            current = under_index[crossing]
    if set(over_arc) != set(under_index):
        raise ArithmeticError("missing overcrossing in traversal")
    result = [[0] * m for _ in range(m)]
    for crossing, i in under_index.items():
        result[i][over_arc[crossing]] += 2
        result[i][(i - 1) % m] -= 1
        result[i][i] -= 1
    return result


def determinant(grid: Grid) -> int:
    matrix = coloring_matrix(grid)
    if not matrix:
        return 1
    return abs(bareiss([row[:-1] for row in matrix[:-1]]))
