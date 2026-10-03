"""Finite-state decision procedure for coefficient-bounded A(X)u(X)=b(X).

A[k][i][j] is the coefficient of X**k in matrix entry (i,j).
b[t][i] is the coefficient of X**t in right-hand component i.
All unknown coefficients belong to {0,...,bound}; their degrees are unbounded.
The implementation is deliberately exhaustive and intended for small examples.
"""
from __future__ import annotations
from collections import deque
from itertools import product
from typing import Sequence


def solve(A: Sequence[Sequence[Sequence[int]]], b: Sequence[Sequence[int]], bound: int
          ) -> list[dict[int, int]] | None:
    if type(bound) is not int or bound < 0 or not A or not A[0] or not A[0][0] or not b:
        raise ValueError("nonempty matrices/right side and a natural bound are required")
    r, n = len(A[0]), len(A[0][0])
    if any(len(matrix) != r or any(len(row) != n for row in matrix) for matrix in A):
        raise ValueError("inconsistent matrix shape")
    if any(len(row) != r for row in b):
        raise ValueError("inconsistent right-hand shape")
    if any(type(c) is not int for matrix in A for row in matrix for c in row):
        raise ValueError("matrix coefficients must be integers")
    if any(type(c) is not int for row in b for c in row):
        raise ValueError("right-hand coefficients must be integers")
    d = len(A) - 1
    symbols = tuple(product(range(bound + 1), repeat=n))
    zero = (0,) * n
    target = (zero,) * d

    def successor(memory, symbol, rhs):
        past = (symbol,) + memory
        if any(sum(A[k][i][j] * past[k][j] for k in range(d + 1) for j in range(n))
               != rhs[i] for i in range(r)):
            return None
        return (symbol,) + memory[:d - 1] if d else ()

    # Store one representative prefix for each reachable memory.
    frontier = {target: ()}
    for rhs in b:
        nxt = {}
        for memory, prefix in frontier.items():
            for symbol in symbols:
                new = successor(memory, symbol, rhs)
                if new is not None and new not in nxt:
                    nxt[new] = prefix + (symbol,)
        frontier = nxt
        if not frontier:
            return None

    queue = deque(frontier)
    paths = dict(frontier)
    while queue:
        memory = queue.popleft()
        if memory == target:
            return [{t: row[j] for t, row in enumerate(paths[memory]) if row[j]}
                    for j in range(n)]
        for symbol in symbols:
            new = successor(memory, symbol, (0,) * r)
            if new is not None and new not in paths:
                paths[new] = paths[memory] + (symbol,)
                queue.append(new)
    return None
