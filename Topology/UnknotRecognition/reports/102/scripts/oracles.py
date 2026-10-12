"""Small independent exhaustive oracles; exponential, never production code."""
from functools import lru_cache
from itertools import combinations, permutations


def sparse(a):
    return {i: {j: x for j, x in enumerate(row) if x} for i, row in enumerate(a)}


def pivot(a, r, c):
    return tuple(tuple(min(2, a[i][j] + a[i][c] * a[r][j])
                       for j in range(len(a[0])) if j != c)
                 for i in range(len(a)) if i != r)


@lru_cache(maxsize=None)
def max_pivots(a):
    if not a:
        return 0
    best = 0
    for r, row in enumerate(a):
        for c, v in enumerate(row):
            if v == 1:
                best = max(best, 1 + max_pivots(pivot(a, r, c)))
                if best == len(a):
                    return best
    return best


def permanent_one_minor(a):
    m = len(a)
    n = len(a[0]) if m else 0
    if not m:
        return True
    for selected in combinations(range(n), m):
        total = 0
        for perm in permutations(selected):
            product = 1
            for i, c in enumerate(perm):
                product *= a[i][c]
            total += product
            if total > 1:
                break
        if total == 1:
            return True
    return False


def stopping_subsets(a):
    m = len(a)
    n = len(a[0]) if m else 0
    answer = []
    for mask in range(1, 1 << m):
        selected = [i for i in range(m) if mask >> i & 1]
        if all(sum(a[i][j] for i in selected) != 1 for j in range(n)):
            answer.append(selected)
    return answer
