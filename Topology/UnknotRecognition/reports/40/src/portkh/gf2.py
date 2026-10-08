"""Exact binary matrices, stored as integer rows (least significant bit = column 0).

All public matrix operations carry dimensions where an empty matrix would otherwise
lose them. The algorithms deliberately use elementary elimination, not floating point.
"""
from __future__ import annotations
from collections.abc import Iterable, Sequence


def check_rows(rows: Sequence[int], width: int) -> None:
    if type(width) is not int or width < 0:
        raise ValueError('matrix width must be a nonnegative integer')
    if any(type(v) is not int or v < 0 or v.bit_length() > width for v in rows):
        raise ValueError('invalid binary matrix row')


def bits(value: int):
    while value:
        bit = value & -value
        yield bit.bit_length() - 1
        value ^= bit


def row_mul(row: int, matrix: Sequence[int]) -> int:
    result = 0
    for j in bits(row):
        result ^= matrix[j]
    return result


def mul(left: Sequence[int], right: Sequence[int]) -> list[int]:
    return [row_mul(row, right) for row in left]


def transpose(rows: Sequence[int], width: int) -> list[int]:
    result = [0] * width
    for i, row in enumerate(rows):
        for j in bits(row):
            result[j] |= 1 << i
    return result


def add(left: Sequence[int], right: Sequence[int]) -> list[int]:
    if len(left) != len(right):
        raise ValueError('different matrix heights')
    return [a ^ b for a, b in zip(left, right)]


def identity(n: int) -> list[int]:
    return [1 << i for i in range(n)]


def independent_indices(rows: Sequence[int]) -> list[int]:
    """Indices of independent original rows, not of row-reduced substitutes."""
    basis: dict[int, int] = {}
    selected = []
    for i, value in enumerate(rows):
        v = value
        while v:
            pivot = v.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = v
                selected.append(i)
                break
            v ^= basis[pivot]
    return selected


def independent(rows: Sequence[int]) -> list[int]:
    return [rows[i] for i in independent_indices(rows)]


def rank(rows: Iterable[int]) -> int:
    basis: dict[int, int] = {}
    for value in rows:
        v = value
        while v:
            pivot = v.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = v
                break
            v ^= basis[pivot]
    return len(basis)


def inverse(rows: Sequence[int]) -> list[int]:
    n = len(rows)
    check_rows(rows, n)
    work = [rows[i] | (1 << (n + i)) for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if work[i] >> j & 1), None)
        if pivot is None:
            raise ValueError('singular binary matrix')
        work[j], work[pivot] = work[pivot], work[j]
        for i in range(n):
            if i != j and work[i] >> j & 1:
                work[i] ^= work[j]
    return [v >> n for v in work]


def generalized_inverse(rows: Sequence[int], width: int) -> tuple[list[int], int]:
    """Return h with A h A=A and h A h=h; A is m by width, h is width by m.

    An invertible rank minor gives h = E_J A[I,J]^{-1} E_I^T.
    This is a reflexive generalized inverse, not a Moore-Penrose inverse.
    """
    check_rows(rows, width)
    columns = transpose(rows, width)
    js = independent_indices(columns)
    q = len(js)
    selected_columns = [sum(((row >> j) & 1) << k for k, j in enumerate(js))
                        for row in rows]
    ii = independent_indices(selected_columns)
    if len(ii) != q:
        raise ArithmeticError('inconsistent rank minor')
    inv = inverse([selected_columns[i] for i in ii])
    h = [0] * width
    for a, j in enumerate(js):
        h[j] = sum(((inv[a] >> b) & 1) << i for b, i in enumerate(ii))
    return h, q


def rank_factor(rows: Sequence[int], width: int) -> tuple[list[int], list[int]]:
    """A=U V with U chosen independent columns and V scalar coordinate rows."""
    check_rows(rows, width)
    h, q = generalized_inverse(rows, width)
    js = independent_indices(transpose(rows, width))
    u = [sum(((row >> j) & 1) << k for k, j in enumerate(js)) for row in rows]
    # H A, restricted to selected column indices, gives all column coordinates.
    ha = mul(h, rows)
    v = [ha[j] for j in js]
    if len(v) != q:
        raise ArithmeticError('rank factor size mismatch')
    return u, v


def border_core(u0_rows: Sequence[int], v0_columns: Sequence[int],
                middle: Sequence[int], r: int) -> tuple[list[int], int, int]:
    """Build [[0,Ubar],[Vbar,middle]] after deleting only zero redundant directions."""
    ubar = independent(u0_rows)
    vcols = independent(v0_columns)
    a, b = len(ubar), len(vcols)
    vbar = transpose(vcols, r)
    core = [row << b for row in ubar]
    core += [vbar[j] | (middle[j] << b) for j in range(r)]
    return core, a, b


def rank_update(a: Sequence[int], ncols: int, u: Sequence[int],
                v: Sequence[int]) -> dict:
    """Exact rank of A+UV, including singular I+VhU and rectangular A."""
    m, r = len(a), len(v)
    check_rows(a, ncols)
    check_rows(u, r)
    check_rows(v, ncols)
    if len(u) != m:
        raise ValueError('U and A have different row counts')
    h, q = generalized_inverse(a, ncols)
    hu = mul(h, u)
    u0 = add(u, mul(a, hu))
    v0 = add(v, mul(mul(v, h), a))
    middle = add(identity(r), mul(v, hu))
    core, aa, bb = border_core(u0, transpose(v0, ncols), middle, r)
    rk = rank(core)
    result = q + rk - r
    if not 0 <= result <= min(m, ncols):
        raise ArithmeticError('impossible updated rank')
    return {'rank': result, 'base_rank': q, 'ports': r,
            'left_quotient_rank': aa, 'right_quotient_rank': bb,
            'core_rank': rk, 'core_rows': core, 'core_shape': [aa+r, bb+r],
            'middle_rows': middle}
