"""Bounded-exception atlas, using capped coefficients and sparse support.

None means support > k+1. A tuple ((owner,weight),...) is sorted, has
weights 1 or 2, and has at most k+1 distinct owners. No signed operations.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Sequence, Mapping
from .core import Program, nat, sparse_rows

Signature = tuple[tuple[int, int], ...] | None


def merge(a: Signature, b: Signature, limit: int) -> Signature:
    if a is None or b is None:
        return None
    ans = []
    i = j = 0
    while i < len(a) or j < len(b):
        if j == len(b) or (i < len(a) and a[i][0] < b[j][0]):
            ans.append(a[i]); i += 1
        elif i == len(a) or b[j][0] < a[i][0]:
            ans.append(b[j]); j += 1
        else:
            ans.append((a[i][0], min(2, a[i][1] + b[j][1])))
            i += 1; j += 1
        if len(ans) > limit:
            return None
    return tuple(ans)


def multiply(a: Signature, w: int) -> Signature:
    if w == 0:
        return ()
    if a is None or w == 1:
        return a
    return tuple((i, 2) for i, _ in a)


@dataclass(frozen=True)
class Atlas:
    k: int
    q: int
    survivors: tuple[int, ...]
    signatures: tuple[Signature, ...]


def build_atlas(p: Program, passive: Sequence[Mapping[int, int]], k: int) -> Atlas:
    nat(k, "exception budget")
    rows = sparse_rows(passive, p.n)
    if k > len(rows):
        raise ValueError("budget exceeds passive row count")
    states: list[Signature] = [()] * p.n
    for i, row in enumerate(rows):
        for h, w in row.items():
            states[h] = merge(states[h], ((i, min(2, w)),), k + 1)
    for t, (_, g) in enumerate(p.pivots):
        for h, w in p.successors[t]:
            states[h] = merge(states[h], multiply(states[g], w), k + 1)
        states[g] = ()
    return Atlas(k, len(rows), p.survivors, tuple(states))


def query_atlas(a: Atlas, deleted: Iterable[int] = ()) -> tuple[int, ...]:
    d = frozenset(deleted)
    if any(type(i) is not int or not 0 <= i < a.q for i in d) or len(d) > a.k:
        raise ValueError("invalid deleted-owner set")
    ans = [-1] * a.q
    for h in a.survivors:
        sig = a.signatures[h]
        if sig is None:
            continue
        survivors = [(i, w) for i, w in sig if i not in d]
        if len(survivors) == 1 and survivors[0][1] == 1:
            i = survivors[0][0]
            if ans[i] == -1:
                ans[i] = h
    return tuple(ans)


def find_exceptions(a: Atlas, *, node_cap: int | None = None) -> dict:
    """Complete (n+1)^k search, or explicit INCONCLUSIVE under a node cap.

    FOUND means the surviving passive subfamily passes the fixed-disk test.
    It does not permit omitting actual topological attachments.
    """
    if node_cap is not None:
        nat(node_cap, "node cap")
    candidates: list[list[frozenset[int]]] = [[] for _ in range(a.q)]
    for h in a.survivors:
        sig = a.signatures[h]
        if sig is not None:
            support = frozenset(i for i, _ in sig)
            for i, w in sig:
                if w == 1:
                    candidates[i].append(support - {i})
    stack = [frozenset()]
    visited = set()
    nodes = 0
    while stack:
        d = stack.pop()
        if d in visited:
            continue
        if node_cap is not None and nodes >= node_cap:
            return {"status": "INCONCLUSIVE", "nodes": nodes}
        visited.add(d); nodes += 1
        private = query_atlas(a, d)
        missing = next((i for i, h in enumerate(private) if i not in d and h == -1), None)
        if missing is None:
            return {"status": "FOUND", "deleted": sorted(d),
                    "least_private": list(private), "nodes": nodes}
        choices = {d | {missing}}
        choices.update(d | s for s in candidates[missing])
        choices = {x for x in choices if len(d) < len(x) <= a.k}
        # Deterministic order; queue/set mechanics are not a worst-case hashing claim.
        stack.extend(sorted(choices, key=lambda x: (len(x), tuple(sorted(x))), reverse=True))
    return {"status": "NO_SUBFAMILY_WITHIN_BUDGET", "nodes": nodes}
