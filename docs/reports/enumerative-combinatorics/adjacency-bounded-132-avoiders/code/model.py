"""Exact combinatorics for adjacency-bounded 132-avoiding permutations.

The endpoint recurrence is due to Mayama and Akita (arXiv:2605.23519v1).
All integer calculations use the Python standard library. None of the routines
below infer a recurrence from data.
"""
from __future__ import annotations

from functools import lru_cache
from itertools import permutations
from math import comb
from typing import Dict, Iterable, List, Optional, Tuple

State = Tuple[Optional[int], Optional[int]]  # None denotes infinity.
Edge = Tuple[int, int, int, int]  # row, column, degree, multiplicity


def catalan(n: int) -> int:
    if n < 0:
        raise ValueError("Catalan index must be nonnegative")
    return comb(2 * n, n) // (n + 1)


def avoids132(p: Tuple[int, ...]) -> bool:
    """A direct definition-based test, deliberately independent of the DP."""
    return not any(p[i] < p[k] < p[j]
                   for i in range(len(p))
                   for j in range(i + 1, len(p))
                   for k in range(j + 1, len(p)))


@lru_cache(maxsize=None)
def av132(n: int) -> Tuple[Tuple[int, ...], ...]:
    """Generate each avoider once by its maximum decomposition."""
    if n < 0:
        raise ValueError("Length must be nonnegative")
    if n == 0:
        return ((),)
    result = []
    for ell in range(n):
        r = n - 1 - ell
        for left in av132(ell):
            for right in av132(r):
                result.append(tuple(x + r for x in left) + (n,) + right)
    return tuple(result)


@lru_cache(maxsize=None)
def first_count(k: int, d: int) -> int:
    """Av_{k-1}(132) with first value k-d; 1 <= d <= k-1."""
    if k < 2 or not 1 <= d <= k - 1:
        return 0
    numerator = d * comb(2 * k - d - 3, k - 2)
    assert numerator % (k - 1) == 0
    return numerator // (k - 1)


@lru_cache(maxsize=None)
def c(k: int, p: Optional[int]) -> int:
    """The cumulative coefficient c_{k,p} in the endpoint recurrence."""
    if k < 1 or (p is not None and p < 0):
        return 0
    if k == 1:
        return 1
    if p is None or p >= k - 1:
        return catalan(k - 1)
    return sum(first_count(k, d) for d in range(1, p + 1))


def states(m: int, component: str = "all") -> List[State]:
    if m < 1:
        raise ValueError("m must be positive")
    if component == "U":
        return [(p, None) for p in range(m)]
    if component == "V":
        if m < 2:
            raise ValueError("V is used only for m >= 2")
        return [(p, q) for p in range(m) for q in range(p)] + \
               [(p, m - 1) for p in range(m - 1)]
    if component != "all":
        raise ValueError("component must be all, U, or V")
    b: List[Optional[int]] = list(range(m)) + [None]
    return [(p, q) for p in b for q in b]


def sub(p: Optional[int], k: int) -> Optional[int]:
    return None if p is None else p - k


def edges(m: int, component: str = "all") -> Tuple[List[State], List[Edge]]:
    ss = states(m, component)
    index = {s: i for i, s in enumerate(ss)}
    es: List[Edge] = []
    for row, (p, q) in enumerate(ss):
        for k in range(1, m + 1):
            target = (m - k, sub(q, k))
            coeff = c(k, p)
            if coeff and target in index:
                es.append((row, index[target], k, coeff))
        target = (sub(p, 1), m - 1)
        if target in index:
            es.append((row, index[target], 1, 1))
    return ss, es


def endpoint_counts(m: int, nmax: int) -> Tuple[List[State], List[List[int]]]:
    """All cumulative endpoint states; column zero is unused and set to zero."""
    if nmax < 1:
        raise ValueError("nmax must be >= 1")
    ss, es = edges(m)
    out = [[0] * (nmax + 1) for _ in ss]
    for row in out:
        row[1] = 1
    for n in range(2, nmax + 1):
        for row, col, k, coeff in es:
            if n - k >= 1:
                out[row][n] += coeff * out[col][n - k]
    return ss, out


def counts(m: int, nmax: int) -> List[int]:
    if nmax < 0:
        raise ValueError("nmax must be nonnegative")
    if nmax == 0:
        return [1]
    ss, cc = endpoint_counts(m, nmax)
    out = cc[ss.index((None, None))].copy()
    out[0] = 1
    return out


def majorant_counts(m: int, nmax: int) -> List[int]:
    """Coefficients of 1 + x/(1 - x - sum C_{k-1} x^k)."""
    out = [0] * (nmax + 1)
    out[0] = 1
    if nmax:
        out[1] = 1
    for n in range(2, nmax + 1):
        out[n] = out[n - 1] + sum(catalan(k - 1) * out[n - k]
                                  for k in range(1, min(m, n - 1) + 1))
    return out


def block_counts(m: int, d: int, nmax: int) -> List[int]:
    """Coefficients of the injective skew-block construction, 1/(1-K_{m,d})."""
    if not 1 <= d < m:
        raise ValueError("Require 1 <= d < m")
    out = [0] * (nmax + 1)
    out[0] = 1
    for n in range(1, nmax + 1):
        out[n] = sum(c(k, d) * out[n - k]
                     for k in range(1, min(m - d, n) + 1))
    return out


def is_strongly_connected(size: int, es: List[Edge]) -> bool:
    for reverse in (False, True):
        graph = [[] for _ in range(size)]
        for a, b, _, _ in es:
            if reverse:
                a, b = b, a
            graph[a].append(b)
        reached, stack = {0}, [0]
        while stack:
            for v in graph[stack.pop()]:
                if v not in reached:
                    reached.add(v)
                    stack.append(v)
        if len(reached) != size:
            return False
    return True


def verify_shift(m: int, component: str) -> int:
    """Verify coefficientwise principal-submatrix domination exactly."""
    small, ee = edges(m, component)
    large, ff = edges(m + 1, component)
    lift = lambda s: tuple(None if t is None else t + 1 for t in s)
    mapping = [large.index(lift(s)) for s in small]
    assert len(set(mapping)) == len(small) < len(large)
    dd: Dict[Tuple[int, int, int], int] = {}
    for a, b, k, coeff in ff:
        dd[a, b, k] = dd.get((a, b, k), 0) + coeff
    for a, b, k, coeff in ee:
        key = (mapping[a], mapping[b], k)
        assert dd.get(key, 0) >= coeff, (m, component, key)
    assert is_strongly_connected(len(small), ee)
    assert is_strongly_connected(len(large), ff)
    return len(ee)
