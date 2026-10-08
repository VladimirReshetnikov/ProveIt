"""Independent scalar hypercube oracle over F2, for small-diagram validation.

No dotted-cobordism gluing or scanning code is used in this module.
"""
from __future__ import annotations
from collections import defaultdict
from .diagrams import DSU
from .geometry import SMOOTHINGS, ScanLimit

def state_circles(pd, state):
    n = len(pd)
    dsu = DSU(2 * n)
    for i, row in enumerate(pd):
        for a, b in SMOOTHINGS[(state >> i) & 1]:
            dsu.union(row[a], row[b])
    groups = defaultdict(set)
    for e in range(2 * n):
        groups[dsu.find(e)].add(e)
    keys = tuple(sorted((frozenset(v) for v in groups.values()), key=min))
    return keys, {e: i for i, circle in enumerate(keys) for e in circle}

def edge_images(source, target, lab):
    sk, so = source
    tk, to = target
    links = [{to[e] for e in c} for c in sk]
    if len(tk) == len(sk) - 1:
        target_labels = [0] * len(tk)
        for i, dests in enumerate(links):
            if len(dests) != 1:
                raise ArithmeticError('invalid merge')
            target_labels[next(iter(dests))] += (lab >> i) & 1
        if max(target_labels, default=0) >= 2:
            return ()
        return (sum(x << i for i, x in enumerate(target_labels)),)
    if len(tk) != len(sk) + 1:
        raise ArithmeticError('saddle does not change circle count by one')
    split = next(i for i, dests in enumerate(links) if len(dests) == 2)
    fixed = 0
    for i, dests in enumerate(links):
        if i != split and (lab >> i) & 1:
            fixed |= 1 << next(iter(dests))
    a, b = sorted(links[split])
    if (lab >> split) & 1:
        return (fixed | (1 << a) | (1 << b),)
    return (fixed | (1 << a), fixed | (1 << b))

def rank(columns):
    pivots = {}
    for col in columns:
        while col:
            p = col.bit_length() - 1
            if p not in pivots:
                pivots[p] = col
                break
            col ^= pivots[p]
    return len(pivots)

def cube_ranks(diagram, *, check_square=True, max_basis=200000):
    pd, n = diagram.pd, len(diagram.pd)
    if not n:
        return {0: 2}
    states = [state_circles(pd, s) for s in range(1 << n)]
    by_degree, indices = defaultdict(list), {}
    count = 0
    for s, (keys, _) in enumerate(states):
        r = s.bit_count()
        for lab in range(1 << len(keys)):
            indices[s, lab] = len(by_degree[r])
            by_degree[r].append((s, lab))
            count += 1
            if count > max_basis:
                raise ScanLimit('cube-oracle basis ceiling')
    columns = {}
    for r, basis in by_degree.items():
        cols = []
        for s, lab in basis:
            col = 0
            for i in range(n):
                if not (s >> i) & 1:
                    t = s | (1 << i)
                    for target_lab in edge_images(states[s], states[t], lab):
                        col ^= 1 << indices[t, target_lab]
            cols.append(col)
        columns[r] = cols
    if check_square:
        for r, cols in columns.items():
            next_cols = columns.get(r + 1, [])
            for col in cols:
                value = 0
                while col:
                    bit = col & -col
                    value ^= next_cols[bit.bit_length() - 1]
                    col ^= bit
                if value:
                    raise ArithmeticError('cube differential does not square to zero')
    ranks = {r: rank(cols) for r, cols in columns.items()}
    return {r: dim for r, basis in by_degree.items()
            if (dim := len(basis) - ranks.get(r, 0) - ranks.get(r - 1, 0))}
