"""Literal exhaustive reference paths, independent of the optimized producer."""
from itertools import combinations, product


def independent(inst, labels):
    labels = list(labels)
    if len(set(labels)) != len(labels):
        return False
    adjacency = [[] for _ in range(inst.vertices)]
    for e in labels:
        u, v = inst.edges[e]
        seen, stack = {u}, [u]
        while stack:
            for x in adjacency[stack.pop()]:
                if x not in seen:
                    seen.add(x)
                    stack.append(x)
        if v in seen:
            return False
        adjacency[u].append(v)
        adjacency[v].append(u)
    return True


def deleted_closure(inst, seeds):
    deleted = set(seeds)
    while True:
        found = None
        for h in range(inst.columns):
            remaining = [(e, inst.matrix[e][h]) for e in range(inst.m) if e not in deleted]
            if sum(value for _, value in remaining) == 1:
                found = next(e for e, value in remaining if value == 1)
                break
        if found is None:
            return deleted
        deleted.add(found)


def literal_trees(inst):
    for chosen in combinations(range(inst.m), inst.vertices - 1):
        if independent(inst, chosen):
            yield chosen


def brute_solve(inst):
    trials = 0
    for chosen in literal_trees(inst):
        trials += 1
        if len(deleted_closure(inst, chosen)) == inst.m:
            return True, chosen, trials
    return False, None, trials


def brute_representatives(inst, groups, fixed=()):
    for choice in product(*(sorted(g) for g in groups)):
        if len(set(choice)) == len(choice) and independent(inst, (*fixed, *choice)):
            return choice
    return None


def brute_projected(act, vectors, p, rank):
    # Uses independent scalar Gaussian elimination, not exterior coordinates.
    def scalar_rank(chosen):
        rows = [list(vectors[e]) for e in chosen]
        rank = 0
        for h in range(len(vectors[0]) if vectors else 0):
            pivot = next((i for i in range(rank, len(rows)) if rows[i][h] % p), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            inv = pow(rows[rank][h] % p, -1, p)
            rows[rank] = [x * inv % p for x in rows[rank]]
            for i in range(rank + 1, len(rows)):
                c = rows[i][h]
                rows[i] = [(a - c * b) % p for a, b in zip(rows[i], rows[rank])]
            rank += 1
        return rank
    for k in range(rank + 1):
        for chosen in combinations(range(len(vectors)), k):
            if act.seed_closure(chosen) == act.full and scalar_rank(chosen) == k:
                return chosen
    return None
