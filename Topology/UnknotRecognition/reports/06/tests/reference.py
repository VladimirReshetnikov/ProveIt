"""Small, deliberately slow test oracle, independent of production DSU/saddles.

This is a second construction of the same mathematical complex, not an
independent theorem prover or an external knot package. Use only on tiny PDs.
"""
from itertools import product


def smoothing(pd, mask):
    adjacency = {edge: [] for c in pd for edge in c}
    if not pd:
        return [frozenset({0})]
    for i, (a, b, c, d) in enumerate(pd):
        pairs = [(a, d), (b, c)] if mask >> i & 1 else [(a, b), (c, d)]
        for u, v in pairs:
            adjacency[u].append(v)
            adjacency[v].append(u)
    remaining = set(adjacency)
    components = []
    while remaining:
        pending, found = [min(remaining)], set()
        while pending:
            vertex = pending.pop()
            if vertex in found:
                continue
            found.add(vertex)
            pending.extend(adjacency[vertex])
        remaining -= found
        components.append(frozenset(found))
    return components


def differential(pd, height):
    n = len(pd)
    resolutions = [smoothing(pd, mask) for mask in range(2**n)]
    basis = [[] for _ in range(n + 1)]
    for mask, circles in enumerate(resolutions):
        for tail in product((0, 1), repeat=len(circles) - 1):
            basis[bin(mask).count("1")].append((mask, (1,) + tail))
    if height == n:
        return [[0] * 0 for _ in basis[height]]
    target_index = {v: i for i, v in enumerate(basis[height + 1])}
    columns = []
    for mask, values in basis[height]:
        source = resolutions[mask]
        column = [0] * len(target_index)
        for crossing in range(n):
            if mask >> crossing & 1:
                continue
            target_mask = mask | (1 << crossing)
            target = resolutions[target_mask]
            terms = [{}]
            for j, circle in enumerate(target):
                overlaps = [i for i, old in enumerate(source) if old & circle]
                if len(overlaps) == 2:
                    x, y = [values[i] for i in overlaps]
                    if x == y == 1:
                        terms = []
                        break
                    for term in terms:
                        term[j] = x | y
                elif circle in source:
                    for term in terms:
                        term[j] = values[source.index(circle)]
            affected = [j for j in range(len(target)) if terms and j not in terms[0]]
            if affected:
                a, b = affected
                old = next(i for i, c in enumerate(source) if c & target[a])
                choices = [(1, 1)] if values[old] else [(0, 1), (1, 0)]
                terms = [term | {a: x, b: y}
                         for term in terms for x, y in choices]
            for term in terms:
                labels = tuple(term[i] for i in range(len(target)))
                column[target_index[target_mask, labels]] ^= 1
        columns.append(column)
    return columns


def dense_rank(columns):
    """Ordinary list-of-bits Gaussian elimination, unlike bitset production code."""
    if not columns:
        return 0
    matrix = [list(row) for row in zip(*columns)]
    rank = 0
    for col in range(len(columns)):
        pivot = next((r for r in range(rank, len(matrix)) if matrix[r][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for row in range(rank + 1, len(matrix)):
            if matrix[row][col]:
                matrix[row] = [x ^ y for x, y in zip(matrix[row], matrix[rank])]
        rank += 1
    return rank
