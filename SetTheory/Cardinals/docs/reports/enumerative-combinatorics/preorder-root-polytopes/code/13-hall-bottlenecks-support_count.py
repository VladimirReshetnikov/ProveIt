#!/usr/bin/env python3
"""Exact weighted matching-support counts, not counts of individual matchings.

Standard-library-only reference implementation of the cover-type formula in
article.tex. All numeric inputs are positive integers or fractions.Fraction.
The algorithm is fixed-parameter tractable in the maximum matching size.
It is a reference implementation, not a performance-optimized solver.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from fractions import Fraction
from itertools import combinations_with_replacement
from math import comb
from typing import Iterable, Sequence

Number = int | Fraction


def validate(adj: Sequence[Iterable[int]], right_size: int,
             left_weights: Sequence[Number] | None = None,
             right_weights: Sequence[Number] | None = None
             ) -> tuple[list[tuple[int, ...]], list[Fraction], list[Fraction]]:
    if not isinstance(right_size, int) or right_size < 0:
        raise ValueError("right_size must be a nonnegative integer")
    rows = []
    for row in adj:
        row = tuple(sorted(set(row)))
        if any(not isinstance(j, int) or not 0 <= j < right_size for j in row):
            raise ValueError("adjacency entries must be valid right-vertex indices")
        rows.append(row)
    def weights(values: Sequence[Number] | None, size: int) -> list[Fraction]:
        if values is None:
            return [Fraction(1)] * size
        if len(values) != size:
            raise ValueError("weight vector has the wrong length")
        if any(not isinstance(v, (int, Fraction)) or v <= 0 for v in values):
            raise ValueError("weights must be positive integers or Fractions")
        return [Fraction(v) for v in values]
    return rows, weights(left_weights, len(rows)), weights(right_weights, right_size)


def maximum_matching_cover(adj: Sequence[Sequence[int]], right_size: int
                           ) -> tuple[list[int], list[int], list[int], list[int]]:
    """Return left/right mates and a minimum cover, by augmenting paths."""
    m = len(adj)
    ml = [-1] * m
    mr = [-1] * right_size
    # One multi-source breadth-first search per augmentation: O((N+E)r).
    while True:
        queue = deque(x for x in range(m) if ml[x] < 0)
        seen_x = set(queue)
        parent_y = [-1] * right_size
        endpoint = -1
        while queue and endpoint < 0:
            x = queue.popleft()
            for y in adj[x]:
                if parent_y[y] >= 0 or y == ml[x]:
                    continue
                parent_y[y] = x
                if mr[y] < 0:
                    endpoint = y
                    break
                if mr[y] not in seen_x:
                    seen_x.add(mr[y])
                    queue.append(mr[y])
        if endpoint < 0:
            break
        y = endpoint
        while y >= 0:
            x = parent_y[y]
            old_y = ml[x]
            ml[x], mr[y] = y, x
            y = old_y
    zx = {x for x in range(m) if ml[x] < 0}
    zy: set[int] = set()
    queue = deque(zx)
    while queue:
        x = queue.popleft()
        for y in adj[x]:
            if y == ml[x] or y in zy:
                continue
            zy.add(y)
            if mr[y] >= 0 and mr[y] not in zx:
                zx.add(mr[y])
                queue.append(mr[y])
    cx = [x for x in range(m) if x not in zx]
    cy = sorted(zy)
    assert len(cx) + len(cy) == sum(y >= 0 for y in ml)
    assert all(x in cx or y in cy for x, row in enumerate(adj) for y in row)
    return ml, mr, cx, cy


def elementary(weights: Sequence[Fraction], degree: int) -> list[Fraction]:
    e = [Fraction(1)] + [Fraction(0)] * degree
    used = 0
    for w in weights:
        used += 1
        for j in range(min(used, degree), 0, -1):
            e[j] += w * e[j - 1]
    return e


def profiles(groups: dict[tuple[int, ...], list[Fraction]], cap: int
             ) -> list[tuple[tuple[tuple[int, ...], ...], Fraction]]:
    """Each tuple of types denotes selected indistinguishable copies.

    The weight is the elementary-symmetric sum over all actual vertex subsets
    with that type multiplicity; a multiplicity is never counted twice.
    """
    types = sorted(groups)
    es = [elementary(groups[t], cap) for t in types]
    out = [((), Fraction(1))]
    for size in range(1, cap + 1):
        for multiset in combinations_with_replacement(range(len(types)), size):
            weight = Fraction(1)
            for index, multiplicity in Counter(multiset).items():
                weight *= es[index][multiplicity]
                if not weight:
                    break
            if weight:
                out.append((tuple(types[i] for i in multiset), weight))
    return out


def selected_core(core: list[int], weights: list[Fraction]
                  ) -> list[tuple[tuple[int, ...], Fraction]]:
    result = []
    for mask in range(1 << len(core)):
        chosen = tuple(v for j, v in enumerate(core) if mask >> j & 1)
        w = Fraction(1)
        for v in chosen:
            w *= weights[v]
        result.append((chosen, w))
    return result


def perfect_matchable(rows: list[list[int]], size: int) -> bool:
    if len(rows) != size:
        return False
    mate = [-1] * size
    def augment(x: int, seen: set[int]) -> bool:
        for y in rows[x]:
            if y in seen:
                continue
            seen.add(y)
            if mate[y] < 0 or augment(mate[y], seen):
                mate[y] = x
                return True
        return False
    return all(augment(x, set()) for x in range(size))


def support_polynomial(adj: Sequence[Iterable[int]], right_size: int,
                       left_weights: Sequence[Number] | None = None,
                       right_weights: Sequence[Number] | None = None
                       ) -> list[Fraction]:
    """Coefficients sum_{I,J matchable} u_I v_J t^|I|, including a_0=1."""
    rows, uw, vw = validate(adj, right_size, left_weights, right_weights)
    _, _, cx, cy = maximum_matching_cover(rows, right_size)
    p, q = len(cx), len(cy)
    r = p + q
    if r == 0:
        return [Fraction(1)]
    cxset, cyset = set(cx), set(cy)
    rowsets = [set(row) for row in rows]
    gx: dict[tuple[int, ...], list[Fraction]] = defaultdict(list)
    gy: dict[tuple[int, ...], list[Fraction]] = defaultdict(list)
    for x, row in enumerate(rows):
        if x not in cxset and row:  # isolates never occur in a matched support
            assert set(row) <= cyset
            gx[tuple(row)].append(uw[x])
    for y in range(right_size):
        if y not in cyset:
            neighbors = tuple(x for x in cx if y in rowsets[x])
            if neighbors:
                gy[neighbors].append(vw[y])
    px, py = profiles(gx, q), profiles(gy, p)
    output = [Fraction(0)] * (r + 1)
    for U, wu in selected_core(cx, uw):
        for V, wv in selected_core(cy, vw):
            for outer_x, wx in px:
                k = len(U) + len(outer_x)
                if k > r:
                    continue
                for outer_y, wy in py:
                    if len(V) + len(outer_y) != k:
                        continue
                    test_rows = []
                    for x in U:
                        neighbors = [i for i, y in enumerate(V) if y in rowsets[x]]
                        neighbors += [len(V) + j for j, typ in enumerate(outer_y)
                                      if x in typ]
                        test_rows.append(neighbors)
                    for typ in outer_x:
                        test_rows.append([i for i, y in enumerate(V) if y in typ])
                    if perfect_matchable(test_rows, k):
                        output[k] += wu * wv * wx * wy
    return output


def brute_force(adj: Sequence[Iterable[int]], right_size: int,
                left_weights: Sequence[Number] | None = None,
                right_weights: Sequence[Number] | None = None) -> list[Fraction]:
    """Independent support enumeration; exponential in both shore sizes."""
    rows, uw, vw = validate(adj, right_size, left_weights, right_weights)
    m = len(rows)
    reachable: list[set[int]] = [set() for _ in range(1 << m)]
    reachable[0] = {0}
    up = [Fraction(1)] * (1 << m)
    vp = [Fraction(1)] * (1 << right_size)
    for mask in range(1, 1 << m):
        bit = mask & -mask
        i = bit.bit_length() - 1
        up[mask] = up[mask ^ bit] * uw[i]
    for mask in range(1, 1 << right_size):
        bit = mask & -mask
        i = bit.bit_length() - 1
        vp[mask] = vp[mask ^ bit] * vw[i]
    out = [Fraction(0)] * (min(m, right_size) + 1)
    out[0] = 1
    for mask in range(1, 1 << m):
        bit = mask & -mask
        i = bit.bit_length() - 1
        for J in reachable[mask ^ bit]:
            for j in rows[i]:
                if not J >> j & 1:
                    reachable[mask].add(J | (1 << j))
        k = mask.bit_count()
        if k < len(out):
            out[k] += up[mask] * sum((vp[J] for J in reachable[mask]), Fraction(0))
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def hall_graph(s: int, n: int) -> list[list[int]]:
    if s < 1 or n < s:
        raise ValueError("require n >= s >= 1")
    # The first n vertices on each shore are outer, the last s are core.
    return [list(range(n, n+s)) for _ in range(n)] + [list(range(n+s)) for _ in range(s)]


def hall_coefficients(s: int, n: int, activity: Number) -> list[Fraction]:
    if s < 1 or n < s or not isinstance(activity, (int, Fraction)) or activity <= 0:
        raise ValueError("require n >= s >= 1 and positive exact activity")
    a = Fraction(activity)
    def choose(n_: int, k_: int) -> int:
        return comb(n_, k_) if 0 <= k_ <= n_ else 0
    return [sum((Fraction(comb(s,u)*comb(s,v)*choose(n,k-u)*choose(n,k-v))
                 * a**(u+v)
                 for u in range(s+1) for v in range(s+1) if u+v >= k), Fraction(0))
            for k in range(2*s+1)]


def ulc_margins(coefficients: Sequence[Number], order: int) -> list[Fraction]:
    if order < len(coefficients) - 1:
        raise ValueError("normalization order must be at least the degree")
    a = list(coefficients) + [0] * (order + 1 - len(coefficients))
    return [Fraction(k*(order-k))*a[k]**2
            - Fraction((k+1)*(order-k+1))*a[k-1]*a[k+1]
            for k in range(1, order)]
