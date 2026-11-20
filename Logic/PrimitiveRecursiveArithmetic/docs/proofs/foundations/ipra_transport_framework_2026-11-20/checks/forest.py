"""Exact finite checks for the forest theorem. Run with Python 3."""
from itertools import permutations, product
from math import prod


def identity(n):
    return tuple(range(n))


def compose(g, f):
    return tuple(g[x] for x in f)


def inverse(f):
    assert set(f) == set(range(len(f)))
    result = [0] * len(f)
    for x, y in enumerate(f):
        result[y] = x
    return tuple(result)


def charts(sizes, edges, actions):
    """Return each vertex's root, root-to-vertex table, and edge loop tables."""
    n = len(sizes)
    roots = [None] * n
    paths = [None] * n
    for _ in range(n):
        for (s, t), f in zip(edges, actions):
            if (roots[s] is None) == (roots[t] is None):
                continue
            if roots[s] is None:
                s, t, f = t, s, inverse(f)
            roots[t] = roots[s]
            paths[t] = compose(f, paths[s])
            break
        else:
            r = roots.index(None)
            roots[r] = r
            paths[r] = identity(sizes[r])
    loops = []
    for (s, t), f in zip(edges, actions):
        assert roots[s] == roots[t]
        loops.append(compose(inverse(paths[t]), compose(f, paths[s])))
    return roots, paths, loops


def sections(sizes, edges, actions):
    roots, paths, loops = charts(sizes, edges, actions)
    fixed = {
        r: [x for x in range(sizes[r])
            if all(M[x] == x for (s, _), M in zip(edges, loops) if roots[s] == r)]
        for r in dict.fromkeys(roots)
    }
    candidates = set()
    for xs in product(*fixed.values()):
        seed = dict(zip(fixed, xs))
        candidates.add(tuple(paths[v][seed[r]] for v, r in enumerate(roots)))
    direct = {xs for xs in product(*(range(d) for d in sizes))
              if all(f[xs[s]] == xs[t] for (s, t), f in zip(edges, actions))}
    assert direct == candidates and len(direct) == prod(map(len, fixed.values()))
    return len(direct)


def all_maps(n, m):
    return product(range(m), repeat=n)


def morphisms(sizes_a, sizes_b, edges, a, b):
    roots, pa, ma = charts(sizes_a, edges, a)
    rb, pb, mb = charts(sizes_b, edges, b)
    assert roots == rb
    reps = list(dict.fromkeys(roots))
    candidates = set()
    for vals in product(*(all_maps(sizes_a[r], sizes_b[r]) for r in reps)):
        k = dict(zip(reps, vals))
        if all(compose(k[roots[s]], f) == compose(g, k[roots[s]])
               for (s, _), f, g in zip(edges, ma, mb)):
            out = tuple(compose(pb[v], compose(k[r], inverse(pa[v])))
                        for v, r in enumerate(roots))
            assert all(out[r] == k[r] for r in reps)
            candidates.add(out)
    direct = {h for h in product(*(all_maps(n, m) for n, m in zip(sizes_a, sizes_b)))
              if all(compose(h[t], f) == compose(g, h[s])
                     for (s, t), f, g in zip(edges, a, b))}
    assert candidates == direct
    return len(direct)


def main():
    # Reversed tree edge, parallel edges, a loop and an isolated vertex.
    edges = [(1, 0), (0, 1), (1, 1)]
    cases = tuple(product(permutations(range(2)), repeat=len(edges)))
    assert sections([], [], []) == 1
    assert sections([0], [], []) == 0
    assert sections([2], [(0, 0)], [(1, 0)]) == 0
    assert sections([2], [(0, 0)], [(0, 1)]) == 2
    counts = [sections([2, 2, 3], edges, x) for x in cases]
    assert sum(counts) == 12
    counts = [morphisms([2, 2, 1], [2, 2, 2], edges, a, b)
              for a in cases for b in cases]
    assert len(cases) == 8
    print(f"Sections: 8 edge assignments and 4 boundary/loop examples passed.")
    print(f"Morphisms: {len(counts)} ordered system pairs, {sum(counts)} maps verified.")


if __name__ == "__main__":
    main()
