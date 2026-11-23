"""Independent checks for degree sequences, graph counting and the two worked graphs."""
from itertools import combinations, combinations_with_replacement, permutations
from math import factorial


def pairs(n):
    return list(combinations(range(n), 2))


def havel_hakimi(degrees):
    active = list(enumerate(degrees))
    edges = []
    while active:
        active.sort(key=lambda pair: (-pair[1], pair[0]))
        vertex, degree = active.pop(0)
        if not 0 <= degree <= len(active):
            return None
        for i in range(degree):
            other, remaining = active[i]
            if remaining <= 0:
                return None
            edges.append(tuple(sorted((vertex, other))))
            active[i] = other, remaining - 1
    return edges


def hand_degrees(n, edges):
    d = [0] * n
    for u, v in edges:
        d[u] += 1
        d[v] += 1
    return tuple(d)


def check_degrees():
    sequences = 0
    for n in range(1, 7):
        edges = pairs(n)
        attainable = set()
        for mask in range(1 << len(edges)):
            ed = [e for i, e in enumerate(edges) if mask >> i & 1]
            attainable.add(tuple(sorted(hand_degrees(n, ed), reverse=True)))
        for seq in combinations_with_repetition(n):
            realization = havel_hakimi(seq)
            assert (realization is not None) == (seq in attainable)
            if realization is not None:
                assert len(realization) == len(set(realization))
                assert hand_degrees(n, realization) == seq
            sequences += 1
    return sequences


def combinations_with_repetition(n):
    for d in combinations_with_replacement(range(n), n):
        yield tuple(reversed(d))


def pair_orbits(perm):
    todo = set(pairs(len(perm)))
    count = 0
    while todo:
        edge = min(todo)
        while edge in todo:
            todo.remove(edge)
            u, v = edge
            edge = tuple(sorted((perm[u], perm[v])))
        count += 1
    return count


def determinant(rows):
    """Fraction-free elimination, independent of graph/tree enumeration."""
    a = [list(row) for row in rows]
    if not a:
        return 1
    divisor, sign = 1, 1
    for j in range(len(a) - 1):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            sign = -sign
        for i in range(j + 1, len(a)):
            for k in range(j + 1, len(a)):
                a[i][k], rem = divmod(a[j][j] * a[i][k] - a[i][j] * a[j][k], divisor)
                assert rem == 0
        divisor = a[j][j]
    return sign * a[-1][-1]


def examples():
    edges = [(1, 2), (1, 5), (2, 3), (2, 5), (3, 4), (4, 5), (4, 6)]
    g = {(u-1,v-1) for u,v in edges}
    assert hand_degrees(6,g) == (2, 3, 2, 3, 3, 1)
    matching = {(0,4),(1,2),(3,5)}
    cover = {1,3,4}
    assert matching <= g and len(set().union(*map(set, matching))) == 6
    assert all({u,v} & cover for u,v in g)
    colors = (0,1,0,1,2,0)
    assert all(colors[u] != colors[v] for u,v in g)
    vertices = [set(p) for p in pairs(5)]
    A = [[int(u.isdisjoint(v)) for v in vertices] for u in vertices]
    for t in range(-4, 8):
        assert determinant([[t * (i == j) - A[i][j] for j in range(10)] for i in range(10)]) == (t-3)*(t-1)**5*(t+2)**4
    assert determinant([[3*(i == j) - A[i][j] for j in range(9)] for i in range(9)]) == 2000
    unlabelled = []
    for n in range(9):
        s = sum(2**pair_orbits(p) for p in permutations(range(n)))
        q, remainder = divmod(s, factorial(n))
        assert remainder == 0
        unlabelled.append(q)
    assert unlabelled == [1,1,2,4,11,34,156,1044,12346]
    print("Six-vertex certificates and Petersen determinant identities verified.")
    print("Unlabelled graph counts for orders 0 through 8:", unlabelled)


if __name__ == "__main__":
    print("Sorted degree sequences checked through order 6:", check_degrees())
    examples()
