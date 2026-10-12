"""Independent finite oracles; not used by the optimized solvers."""
from functools import lru_cache
from itertools import combinations


def peel_literal(counts, deferred):
    rows = {r: dict(row) for r, row in counts.items() if r not in set(deferred)}
    moves = []
    while rows:
        selected = None
        columns = {c for row in rows.values() for c, a in row.items() if a}
        for c in sorted(columns):
            if sum(row.get(c, 0) for row in rows.values()) == 1:
                r = next(r for r, row in rows.items() if row.get(c) == 1)
                selected = r, c; break
        if selected is None:
            break
        r, c = selected; del rows[r]; moves.append([r, c])
        for row in rows.values():
            row.pop(c, None)
    return moves, set(rows)


def optimal_subsets(counts, weights=None):
    labels = sorted(counts)
    if weights is None:
        weights = {r: 1 for r in labels}
    best = (sum(weights.values()), len(labels)); witness = labels
    for mask in range(1 << len(labels)):
        d = [r for i, r in enumerate(labels) if mask >> i & 1]
        cost = sum(weights[r] for r in d), len(d)
        if cost < best and not peel_literal(counts, d)[1]:
            best, witness = cost, d
    return best, witness


def maximum_positive_pivots(dense):
    """Exhaust all legal saturated pivots, not merely private schedules."""
    @lru_cache(None)
    def go(a):
        best = 0
        for r, row in enumerate(a):
            for c, x in enumerate(row):
                if x == 1:
                    b = tuple(tuple(min(2, a[i][j] + a[i][c]*a[r][j])
                                    for j in range(len(row)) if j != c)
                              for i in range(len(a)) if i != r)
                    best = max(best, 1 + go(b))
        return best
    return go(tuple(tuple(min(2, x) for x in row) for row in dense))


def sparse(dense):
    return {r: {c: x for c, x in enumerate(row) if x}
            for r, row in enumerate(dense)}


def dense(counts):
    cols = sorted({c for row in counts.values() for c in row})
    return tuple(tuple(counts[r].get(c, 0) for c in cols) for r in sorted(counts))
