"""Deliberately slow, independently structured small-diagram KH reference.

Uses graph walks (not union-find), explicit tuples of labels (not label masks),
and dense byte matrices with row elimination (not packed column elimination).
Only for tests: no production module imports this file.
"""
from __future__ import annotations
from itertools import product


def dense_rank(matrix: list[list[int]] | list[bytearray], ncols: int) -> int:
    a = [list(row) for row in matrix]
    rank = 0
    for col in range(ncols):
        pivot = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        for i in range(rank + 1, len(a)):
            if a[i][col]:
                for j in range(col, ncols):
                    a[i][j] ^= a[rank][j]
        rank += 1
    return rank


def circles(pd, state):
    if not pd:
        return (frozenset((1,)),)
    adjacency = {e: set() for crossing in pd for e in crossing}
    for bit, (a, b, c, d) in zip(state, pd):
        for x, y in (((a, d), (b, c)) if bit else ((a, b), (c, d))):
            adjacency[x].add(y)
            adjacency[y].add(x)
    remaining, components = set(adjacency), []
    while remaining:
        seed = min(remaining)
        found, stack = {seed}, [seed]
        while stack:
            v = stack.pop()
            for w in adjacency[v] - found:
                found.add(w)
                stack.append(w)
        remaining -= found
        components.append(frozenset(found))
    return tuple(components)


def reference_reduced_rank(pd) -> int:
    n = len(pd)
    resolutions = {s: circles(pd, s) for s in product((0, 1), repeat=n)}
    bases = [[] for _ in range(n + 1)]
    for state, components in resolutions.items():
        for labels in product((0, 1), repeat=len(components) - 1):
            bases[sum(state)].append((state, (1,) + labels))
    ranks = []
    for h in range(n):
        matrix = [bytearray(len(bases[h])) for _ in bases[h + 1]]
        for col, (source_state, source_labels) in enumerate(bases[h]):
            source = resolutions[source_state]
            for row, (target_state, target_labels) in enumerate(bases[h + 1]):
                if sum(a != b for a, b in zip(source_state, target_state)) != 1:
                    continue
                target = resolutions[target_state]
                common = set(source) & set(target)
                if any(source_labels[source.index(c)] != target_labels[target.index(c)]
                       for c in common):
                    continue
                source_changed = [source_labels[i] for i, c in enumerate(source)
                                  if c not in common]
                target_changed = [target_labels[i] for i, c in enumerate(target)
                                  if c not in common]
                if len(source_changed) == 2 and len(target_changed) == 1:
                    value = sum(source_changed)
                    coefficient = value < 2 and target_changed[0] == value
                elif len(source_changed) == 1 and len(target_changed) == 2:
                    coefficient = (sum(target_changed) == 1 if source_changed[0] == 0
                                   else target_changed == [1, 1])
                else:
                    raise AssertionError('Reference saddle is not a merge or split')
                matrix[row][col] = int(coefficient)
        ranks.append(dense_rank(matrix, len(bases[h])))
    return sum(map(len, bases)) - 2 * sum(ranks)
