"""Small exact F2 linear algebra. Matrices are tuples of bit-packed columns."""
from __future__ import annotations
from collections.abc import Iterable

def rank(columns: Iterable[int]) -> int:
    pivots: dict[int, int] = {}
    for v in columns:
        if type(v) is not int or v < 0:
            raise ValueError('columns must be nonnegative integers')
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)

def apply(columns: list[int] | tuple[int, ...], v: int) -> int:
    out = 0
    while v:
        low = v & -v
        out ^= columns[low.bit_length() - 1]
        v ^= low
    return out

def compose(left, right):
    return tuple(apply(left, col) for col in right)

def add(a, b):
    if len(a) != len(b): raise ValueError('shape mismatch')
    return tuple(x ^ y for x, y in zip(a, b))

def identity(n): return tuple(1 << j for j in range(n))
