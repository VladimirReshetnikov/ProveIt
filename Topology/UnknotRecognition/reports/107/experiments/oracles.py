"""Small literal enumeration oracles, intentionally independent of the selector."""
from itertools import combinations
from functools import lru_cache


def graphic_rank(inst, subset):
    components = [{v} for v in range(inst.vertices)]
    for r in subset:
        u, v = inst.edges[r]
        a = next(c for c in components if u in c)
        b = next(c for c in components if v in c)
        if a is not b:
            a.update(b)
            components.remove(b)
    return inst.vertices - len(components)


def literal_peel(inst, deleted):
    live = set(range(inst.m)) - set(deleted)
    rr = [dict(row) for row in inst.rows]
    schedule = []
    while live:
        found = False
        for c in range(inst.columns):
            if sum(rr[r].get(c, 0) for r in live) == 1:
                r = next(r for r in live if rr[r].get(c, 0))
                schedule.append([r, c])
                live.remove(r)
                found = True
                break
        if not found:
            return None
    return schedule


def trees(inst):
    for subset in combinations(range(inst.m), inst.vertices - 1):
        if graphic_rank(inst, subset) == inst.vertices - 1:
            yield subset


def tree_oracle(inst):
    inspected = 0
    for tree in trees(inst):
        inspected += 1
        pivots = literal_peel(inst, tree)
        if pivots is not None:
            return dict(yes=True, tree=list(tree), pivots=pivots, inspected=inspected)
    return dict(yes=False, inspected=inspected)


def defect_oracle(inst):
    best = inst.m
    for tree in trees(inst):
        remaining = set(range(inst.m)) - set(tree)
        for k in range(min(best, len(remaining)) + 1):
            if any(literal_peel(inst, set(tree) | set(extra)) is not None
                   for extra in combinations(sorted(remaining), k)):
                best = min(best, k)
                break
    return best


def transversal_oracle(inst, groups):
    best = 0
    def search(color, selected, count):
        nonlocal best
        if count + len(groups) - color <= best:
            return
        if color == len(groups):
            best = max(best, count)
            return
        for r in groups[color]:
            if r not in selected and graphic_rank(inst, selected | {r}) == count + 1:
                search(color + 1, selected | {r}, count + 1)
        search(color + 1, selected, count)
    search(0, set(), 0)
    return best


@lru_cache(None)
def full_positive_oracle(matrix):
    if not matrix:
        return True
    n = len(matrix[0])
    for r, row in enumerate(matrix):
        for c in range(n):
            if row[c] == 1:
                nxt = tuple(tuple(min(2, matrix[i][j] + matrix[i][c] * matrix[r][j])
                                  for j in range(n) if j != c)
                            for i in range(len(matrix)) if i != r)
                if full_positive_oracle(nxt):
                    return True
    return False
