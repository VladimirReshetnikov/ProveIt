"""Exact private-cocore queries on authenticated unsigned incidence data.

This is an algebraic kernel, not an authenticator of 3-dimensional geometry.
A negative result is not a negative topological certificate.  Every source
entry counts actual unsigned occurrences; signed cancellation is forbidden.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence

SCHEMA = "private-cocore-owner-v1"
EMPTY = -1
MANY = -2


def nat(x: object, name: str = "integer") -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be a nonnegative integer (not bool)")
    return x


def sparse_rows(rows: Sequence[Mapping[int, int]], n: int) -> tuple[dict[int, int], ...]:
    nat(n, "column count")
    ans = []
    for r, row in enumerate(rows):
        if not isinstance(row, Mapping):
            raise ValueError("each row must be a mapping")
        out = {}
        for h, w in row.items():
            nat(h, "column"); nat(w, "incidence")
            if h >= n:
                raise ValueError("column out of range")
            if w:
                out[h] = w
        ans.append(out)
    return tuple(ans)


@dataclass(frozen=True)
class Program:
    """A source-validated zero-fill schedule and its forward dependency DAG."""
    n: int
    pivots: tuple[tuple[int, int], ...]
    successors: tuple[tuple[tuple[int, int], ...], ...]
    survivors: tuple[int, ...]
    source_nonzeros: int


def compile_program(real: Sequence[Mapping[int, int]], n: int,
                    schedule: Sequence[Sequence[int]]) -> Program:
    """Validate a complete mixed row/column zero-fill schedule in one scan.

    Previous pivot columns are discarded, never used as forward targets.
    A pivot is allowed precisely when its live row OR live column is private.
    Nonzero-fill schedules raise ValueError and require a legacy fallback.
    """
    rows = sparse_rows(real, n)
    m = len(rows)
    if len(schedule) != m:
        raise ValueError("schedule must cover every real row")
    tr, tc = [-1] * m, [m] * n
    pivots = []
    for t, pair in enumerate(schedule):
        if not isinstance(pair, (tuple, list)) or len(pair) != 2:
            raise ValueError("pivot must be a pair")
        r, g = pair
        nat(r, "pivot row"); nat(g, "pivot column")
        if r >= m or g >= n or tr[r] != -1 or tc[g] != m:
            raise ValueError("invalid or duplicate pivot")
        if rows[r].get(g, 0) != 1:
            raise ValueError("pivot source entry is not one")
        tr[r], tc[g] = t, t
        pivots.append((r, g))
    late = [False] * m
    succ: list[list[tuple[int, int]]] = [[] for _ in range(m)]
    nonzeros = 0
    for r, row in enumerate(rows):
        t = tr[r]
        for h, w in row.items():
            nonzeros += 1
            if tc[h] > t:
                succ[t].append((h, w))
            elif tc[h] < t:
                late[tc[h]] = True
    for t in range(m):
        if succ[t] and late[t]:
            raise ValueError("schedule has nonzero real fill")
    return Program(n, tuple(pivots), tuple(tuple(x) for x in succ),
                   tuple(h for h in range(n) if tc[h] == m), nonzeros)


def plus(a: int, b: int) -> int:
    if a == EMPTY:
        return b
    if b == EMPTY:
        return a
    return MANY  # even two occurrences owned by the same curve are not private


def scale(a: int, w: int) -> int:
    if not w or a == EMPTY:
        return EMPTY
    return a if w == 1 else MANY


def owners(program: Program, passive: Sequence[Mapping[int, int]]) -> tuple[int, ...]:
    """Final state per source column; deleted columns carry EMPTY.

    States: EMPTY=-1, MANY=-2, otherwise the unique passive row identifier.
    This routine uses the compiled schedule, not a geometric proof.
    """
    rows = sparse_rows(passive, program.n)
    state = [EMPTY] * program.n
    for i, row in enumerate(rows):
        for h, w in row.items():
            state[h] = plus(state[h], i if w == 1 else MANY)
    for t, (_, g) in enumerate(program.pivots):
        v = state[g]
        for h, w in program.successors[t]:
            state[h] = plus(state[h], scale(v, w))
        state[g] = EMPTY
    return tuple(state)


def least_private(program: Program, states: Sequence[int], q: int) -> tuple[int, ...]:
    nat(q, "passive row count")
    if len(states) != program.n:
        raise ValueError("wrong state length")
    ans = [-1] * q
    for h in program.survivors:  # increasing original labels: matches native choice
        i = states[h]
        if i >= 0:
            if i >= q:
                raise ValueError("owner out of range")
            if ans[i] == -1:
                ans[i] = h
    return tuple(ans)


def produce_certificate(real: Sequence[Mapping[int, int]], n: int,
                        passive: Sequence[Mapping[int, int]],
                        schedule: Sequence[Sequence[int]]) -> dict:
    p = compile_program(real, n, schedule)
    private = least_private(p, owners(p, passive), len(passive))
    return {"schema": SCHEMA, "n_columns": n, "n_passive": len(passive),
            "pivots": [list(x) for x in p.pivots], "least_private": list(private)}


def normalize_matching(real: Sequence[Mapping[int, int]], n: int,
                       matching: Sequence[Sequence[int]]) -> tuple[tuple[int, int], ...]:
    """Normalize a source-unit matching, eliminating all real fill.

    Each row is paired with a distinct column whose SOURCE entry equals one.
    Acyclicity of the off-diagonal matched incidence graph is necessary and
    sufficient for these pairs to be a complete positive schedule. On an
    acyclic matching every elimination order is valid and gives the same
    passive counts; this returns a column-private topological order.
    Pivots created from source-zero entries are deliberately unsupported.
    """
    from collections import deque
    rows = sparse_rows(real, n)
    m = len(rows)
    if len(matching) != m:
        raise ValueError('matching must cover every source row')
    column = [-1] * m
    row_for_column = [-1] * n
    for pair in matching:
        if not isinstance(pair, (list, tuple)) or len(pair) != 2:
            raise ValueError('matched pair must have two entries')
        r, g = pair
        nat(r, 'matched row'); nat(g, 'matched column')
        if r >= m or g >= n or column[r] != -1 or row_for_column[g] != -1:
            raise ValueError('duplicate or out-of-range matched pair')
        if rows[r].get(g, 0) != 1:
            raise ValueError('matching is not source-unit')
        column[r], row_for_column[g] = g, r
    indegree, forward = [0] * m, [[] for _ in range(m)]
    for r, row in enumerate(rows):
        for h in row:
            j = row_for_column[h]
            if j >= 0 and j != r:
                forward[r].append(j)
                indegree[j] += 1
    queue = deque(i for i in range(m) if indegree[i] == 0)
    order = []
    while queue:
        r = queue.popleft()
        order.append((r, column[r]))
        for j in forward[r]:
            indegree[j] -= 1
            if indegree[j] == 0:
                queue.append(j)
    if len(order) != m:
        raise ValueError('cyclic source-unit matching')
    return tuple(order)


def produce_matching_certificate(real, n, passive, matching):
    """Certificate for the normalized matching's canonical private witnesses."""
    return produce_certificate(real, n, passive, normalize_matching(real, n, matching))
