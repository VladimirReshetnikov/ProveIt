"""Independent small-instance checks for the matrix–tree and last-exit formulas.

Run with Python 3. No external packages are required. Vertices and edge labels
are ordered. A triple (u, v, w) specifies endpoints and a positive weight.
"""
from itertools import combinations, permutations, product
from math import factorial, prod


def determinant(matrix):
    n = len(matrix)
    result = 0
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i, j in combinations(range(n), 2))
        result += (-1) ** inversions * prod(matrix[i][p[i]] for i in range(n))
    return result


def principal_minor(n, edges, roots, directed):
    lap = [[0] * n for _ in range(n)]
    for u, v, w in edges:
        lap[u][u] += w
        lap[u][v] -= w
        if not directed:
            lap[v][v] += w
            lap[v][u] -= w
    keep = [i for i in range(n) if i not in roots]
    return determinant([[lap[i][j] for j in keep] for i in keep])


def one_root_per_tree(n, chosen, roots):
    blocks = [{v} for v in range(n)]
    for u, v, _ in chosen:
        a = next(block for block in blocks if u in block)
        b = next(block for block in blocks if v in block)
        if a == b:
            return False
        blocks.remove(b)
        a.update(b)
    return all(len(block & roots) == 1 for block in blocks)


def flows_to_roots(n, chosen, roots):
    parents = {u: v for u, v, _ in chosen}
    if set(parents) != set(range(n)) - roots:
        return False
    for v in range(n):
        for _ in range(n):
            v = parents.get(v, v)
        if v not in roots:
            return False
    return True


def forest_count(n, edges, roots, directed):
    check = flows_to_roots if directed else one_root_per_tree
    return sum(prod(w for _, _, w in chosen)
               for chosen in combinations(edges, n - len(roots))
               if check(n, chosen, roots))


def ordered_tours(n, edges, first):
    """Depth-first enumeration of labelled trails with a prescribed first arc."""
    r, dest, _ = edges[first]
    full = (1 << len(edges)) - 1

    def extend(v, mask):
        if mask == full:
            return int(v == r)
        return sum(extend(t, mask | (1 << i))
                   for i, (s, t, _) in enumerate(edges)
                   if s == v and not mask & (1 << i))

    return extend(dest, 1 << first)


def check_instance(n, edges, directed):
    minor_checks = tour_checks = 0
    for flags in product((False, True), repeat=n):
        roots = {v for v in range(n) if flags[v]}
        value = principal_minor(n, edges, roots, directed)
        assert value == forest_count(n, edges, roots, directed), (edges, roots)
        minor_checks += 1
    if directed and edges:
        unit = [(u, v, 1) for u, v, _ in edges]
        outdeg = [sum(u == i for u, _, _ in edges) for i in range(n)]
        indeg = [sum(v == i for _, v, _ in edges) for i in range(n)]
        # Skip inputs with isolated vertices; the theorem uses only the support.
        if outdeg == indeg and all(outdeg):
            for first, (r, _, _) in enumerate(edges):
                trees = principal_minor(n, unit, {r}, True)
                predicted = trees * prod(factorial(d - 1) for d in outdeg)
                assert predicted == ordered_tours(n, edges, first), (edges, first)
                tour_checks += 1
    return minor_checks, tour_checks


def main():
    graphs = minors = tours = 0
    for directed, max_vertices in ((False, 4), (True, 3)):
        for n in range(max_vertices + 1):
            pairs = list(product(range(n), repeat=2) if directed else
                         combinations(range(n), 2))
            for mask in range(1 << len(pairs)):
                edges = [(u, v, i % 3 + 1) for i, (u, v) in enumerate(pairs)
                         if mask & (1 << i)]
                m, t = check_instance(n, edges, directed)
                minors += m
                tours += t
                graphs += 1
    # Parallel arcs/edges, distinct positive weights and loops in both modes.
    parallel = [(0, 1, 2), (0, 1, 3), (1, 0, 5), (1, 0, 7),
                (0, 0, 11), (1, 1, 13)]
    for directed in (False, True):
        m, t = check_instance(2, parallel, directed)
        minors += m
        tours += t
        graphs += 1
    print(f'{graphs} graph instances, {minors} rooted minors, '
          f'{tours} prescribed-first-arc Euler counts verified.')


if __name__ == '__main__':
    main()
