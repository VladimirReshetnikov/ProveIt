#!/usr/bin/env python3
"""Finite cross-checks for the graph chapter. Run with Python 3.10 or later."""
from itertools import combinations, permutations, product
from math import comb, factorial


def powerset(size):
    return range(1 << size)


def edge_indices(vertices):
    return {p: i for i, p in enumerate(combinations(range(vertices), 2))}


def induced_clique_mask(vertices, indices):
    return sum(1 << indices[p] for p in combinations(vertices, 2))


def cycle_masks(n, indices):
    if n < 3:
        return []
    cycles = []
    for tail in permutations(range(1, n)):
        if tail[0] > tail[-1]:
            continue
        cycle = (0,) + tail
        pairs = (tuple(sorted((cycle[i - 1], cycle[i]))) for i in range(n))
        cycles.append(sum(1 << indices[e] for e in pairs))
    return cycles


def turan(n, parts):
    q, s = divmod(n, parts)
    return comb(n, 2) - (parts - s) * comb(q, 2) - s * comb(q + 1, 2)


def check_simple_graphs():
    for n in range(6):
        indices = edge_indices(n)
        graph_count = 1 << len(indices)
        all_cycles = cycle_masks(n, indices)
        triples = [induced_clique_mask(S, indices) for S in combinations(range(n), 3)]
        cliques = {r: [induced_clique_mask(S, indices)
                       for S in combinations(range(n), r + 1)]
                   for r in range(1, max(2, n + 1))}
        maxima = dict.fromkeys(cliques, 0)
        triangle_sum = 0
        for graph in range(graph_count):
            degree = [0] * n
            for (x, y), i in indices.items():
                if graph >> i & 1:
                    degree[x] += 1
                    degree[y] += 1
            triangle_sum += sum(graph & T == T for T in triples)
            assert sum(degree) == 2 * graph.bit_count()
            for r, forbidden in cliques.items():
                if not any(graph & K == K for K in forbidden):
                    maxima[r] = max(maxima[r], graph.bit_count())
                    assert graph.bit_count() <= turan(n, r)
            if n >= 3:
                old_hamiltonian = any(graph & C == C for C in all_cycles)
                for (x, y), i in indices.items():
                    if not graph >> i & 1 and degree[x] + degree[y] >= n:
                        extended = graph | (1 << i)
                        assert old_hamiltonian == any(extended & C == C for C in all_cycles)
        assert 8 * triangle_sum == graph_count * comb(n, 3)
        assert all(maxima[r] == turan(n, r) for r in maxima)
        if n >= 3:
            assert len(all_cycles) * 2 == factorial(n-1)


def check_tournaments():
    for n in range(1, 6):
        indices = edge_indices(n)
        listings = list(permutations(range(n)))
        for mask in powerset(len(indices)):
            def arc(u, v):
                i = indices[tuple(sorted((u, v)))]
                return bool(mask >> i & 1) == (u < v)

            paths = [w for w in listings if all(arc(x, y) for x, y in zip(w, w[1:]))]
            assert len(paths) % 2 == 1
            if n < 3:
                continue
            reachable = [[(u == v or arc(u, v)) for v in range(n)] for u in range(n)]
            for mid in range(n):
                for u in range(n):
                    for v in range(n):
                        reachable[u][v] |= reachable[u][mid] and reachable[mid][v]
            strong = all(all(row) for row in reachable)
            assert strong == any(arc(w[-1], w[0]) for w in paths)


def prufer_decode(n, word):
    live = set(range(n))
    edges = set()
    for i, head in enumerate(word):
        leaf = min(live - set(word[i:]))
        edges.add(tuple(sorted((leaf, head))))
        live.remove(leaf)
    edges.add(tuple(sorted(live)))
    return frozenset(edges)


def prufer_encode(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    word = []
    for _ in range(n - 2):
        leaf = next(u for u in range(n) if len(adj[u]) == 1)
        head = adj[leaf].pop()
        adj[head].remove(leaf)
        word.append(head)
    return tuple(word)


def check_trees():
    for n in range(2, 7):
        trees = set()
        for word in product(range(n), repeat=n - 2):
            tree = prufer_decode(n, word)
            assert len(tree) == n - 1
            assert prufer_encode(n, tree) == word
            for u in range(n):
                assert sum(u in edge for edge in tree) == 1 + word.count(u)
            trees.add(tree)
        assert len(trees) == n ** (n - 2)
        if n <= 5:
            all_edges = list(combinations(range(n), 2))
            for edges in combinations(all_edges, n - 1):
                seen = {0}
                for _ in range(n):
                    for u, v in edges:
                        if u in seen or v in seen:
                            seen.update((u, v))
                assert (len(seen) == n) == (frozenset(edges) in trees)


def check_matching(a, b):
    pairs = list(product(range(a), range(b)))
    for graph in powerset(len(pairs)):
        edges = {edge for i, edge in enumerate(pairs) if graph >> i & 1}
        # Small independent exhaustive optimization of partial injective maps.
        maximum = 0
        for assignment in product(range(-1, b), repeat=a):
            used = [y for y in assignment if y >= 0]
            compatible = all(y < 0 or (x, y) in edges for x, y in enumerate(assignment))
            if compatible and len(set(used)) == len(used):
                maximum = max(maximum, len(used))
        deficiency = 0
        for left_mask in powerset(a):
            neighbors = {y for x, y in edges if left_mask >> x & 1}
            deficiency = max(deficiency, left_mask.bit_count() - len(neighbors))
        minimum_cover = a + b
        for mask in powerset(a + b):
            if all((mask >> x | mask >> (a + y)) & 1 for x, y in edges):
                minimum_cover = min(minimum_cover, mask.bit_count())
        assert maximum == minimum_cover == a - deficiency


def check_ramsey():
    for n, expected in ((5, 12), (6, 0)):
        indices = edge_indices(n)
        triangles = [induced_clique_mask(S, indices) for S in combinations(range(n), 3)]
        without_monochromatic = sum(
            all((graph & tri) not in (0, tri) for tri in triangles)
            for graph in powerset(len(indices))
        )
        assert without_monochromatic == expected


def check_sumfree():
    universe = [x for x in range(-5, 6) if x != 0]
    for mask in range(1, 1 << len(universe)):
        subset = {x for i, x in enumerate(universe) if mask >> i & 1}
        bound = max(map(abs, subset))
        value = 3 * factorial(bound) - 1
        prime = next(p for p in range(2, value + 1) if value % p == 0 and p % 3 == 2
                     and all(p % k for k in range(2, p) if k * k <= p))
        q = (prime - 2) // 3
        candidates = [{x for x in subset if q + 1 <= (t * x) % prime <= 2 * q + 1}
                      for t in range(1, prime)]
        choice = max(candidates, key=len)
        assert 3 * len(choice) > len(subset)
        assert all(x + y not in choice for x in choice for y in choice)


if __name__ == "__main__":
    check_simple_graphs()
    check_tournaments()
    check_trees()
    for sizes in ((0, 2), (2, 0), (2, 3), (3, 3)):
        check_matching(*sizes)
    check_ramsey()
    check_sumfree()
    print("Graph enumeration, closure, Turan, tournaments, Pruefer, matching, Ramsey and sum-free checks passed.")
