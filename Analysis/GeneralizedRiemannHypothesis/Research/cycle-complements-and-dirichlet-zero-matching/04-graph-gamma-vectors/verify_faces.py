"""Exact checks of the face realizations. Python 3.10+; standard library only."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb

class Graph:
    def __init__(self, n, edges):
        self.n = n
        self.pairs = {tuple(sorted(e)) for e in edges}

    def __len__(self):
        return self.n

    def __iter__(self):
        return iter(range(self.n))

    def edges(self):
        return sorted(self.pairs)


def graph_key(graph):
    degree = Counter(u for edge in graph.edges() for u in edge)
    groups = [list(permutations([u for u in graph if degree[u] == d]))
              for d in sorted({degree[u] for u in graph})]
    keys = []
    for partition in product(*groups):
        order = [u for group in partition for u in group]
        keys.append(tuple(tuple(sorted((a,b))) in graph.pairs for a,b in combinations(order,2)))
    return min(keys)


def all_graphs(maximum):
    old = [Graph(0, [])]
    for n in range(1, maximum + 1):
        unique = {}
        for g in old:
            for neighbors in range(1 << (n-1)):
                h = Graph(n,g.edges() + [(u,n-1) for u in g if neighbors & (1 << u)])
                unique.setdefault(graph_key(h),h)
        old = list(unique.values())
        yield from old


def is_bipartite(graph):
    return any(all(((mask >> a) ^ (mask >> b)) & 1 for a,b in graph.edges())
               for mask in range(1 << len(graph)))


def cycle(n):
    return Graph(n, [(i,(i+1) % n) for i in range(n)])



def normal_faces(g, oriented):
    """Group enumerated matchings by endpoint data, keeping minimum binary weight."""
    arcs = sorted(list(g.edges()) + ([(b, a) for a, b in g.edges()] if oriented else []))
    best = {}

    def visit(first, left, right, mask):
        fiber = (left, right) if oriented else left | right
        if fiber not in best or mask < best[fiber]:
            best[fiber] = mask
        used = left | right
        for j in range(first, len(arcs)):
            a, b = arcs[j]
            if not used & ((1 << a) | (1 << b)):
                visit(j + 1, left | (1 << a), right | (1 << b), mask | (1 << j))
    visit(0, 0, 0, 0)
    faces = set(best.values())
    for face in faces:
        for bit in range(len(arcs)):
            if face & (1 << bit):
                assert face ^ (1 << bit) in faces
    return arcs, faces


def vertex_cover(g):
    for r in range(len(g) + 1):
        for subset in combinations(g, r):
            cover = set(subset)
            if all(a in cover or b in cover for a, b in g.edges()):
                return cover


def color_faces(arcs, faces, cover):
    colors = [a if a in cover else b for a, b in arcs]
    for face in faces:
        used = {colors[i] for i in range(len(arcs)) if face & (1 << i)}
        assert len(used) == face.bit_count()


def generators(g, family):
    n = len(g)
    unit = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    steps = set(unit)
    steps.update(tuple(-x for x in v) for v in unit)
    for a, b in g.edges():
        for sign in (-1, 1):
            signs = (-sign,) if family == 'A' else (-1, 1)
            for sign_b in signs:
                steps.add(tuple(sign*x + sign_b*y for x, y in zip(unit[a], unit[b])))
    return steps


def lattice_gamma(g, family):
    """Count k-step balls, extract the lower half of h*, then its gamma vector."""
    d = len(g)
    steps = generators(g, family)
    seen = {tuple([0]*d)}
    shell = seen.copy()
    counts = [1]
    for k in range(1, d//2 + 1):
        new = {tuple(x+y for x, y in zip(v, s)) for v in shell for s in steps} - seen
        seen |= new
        shell = new
        counts.append(len(seen))
    gamma = []
    for k in range(d//2 + 1):
        h = sum((-1)**j * comb(d+1, j) * counts[k-j] for j in range(k+1))
        gamma.append(h - sum(x*comb(d-2*j, k-j) for j, x in enumerate(gamma)))
    return gamma


def is_flag(faces, narcs):
    """All minimal nonfaces >2 would extend some face by one vertex."""
    for face in faces:
        for j in range(narcs):
            new = 1 << j
            if new & face or (new | face) in faces:
                continue
            if all(((1 << i) | new) in faces for i in range(narcs) if (1 << i) & face):
                return False
    return True


def main():
    total = bipartite = colored = 0
    for g in all_graphs(6):
        if len(g) == 0 or len(g) > 6:
            continue
        total += 1
        arcs, faces = normal_faces(g, oriented=True)
        expected = lattice_gamma(g, 'A')
        sizes = Counter(f.bit_count() for f in faces)
        assert expected == [sizes[j] for j in range(len(expected))]
        nu = max(sizes)
        cover = vertex_cover(g)
        if len(cover) == nu:
            color_faces(arcs, faces, cover)
            colored += 1
        if is_bipartite(g):
            bipartite += 1
            arcs_b, faces_b = normal_faces(g, oriented=False)
            color_faces(arcs_b, faces_b, cover)
            sizes_b = Counter(f.bit_count() for f in faces_b)
            assert lattice_gamma(g, 'B') == [4**j*sizes_b[j] for j in range(len(expected))]
    print(f"All isomorphism classes, 1 to 6 vertices: {total} type-A lattice/face comparisons.")
    print(f"Minimum-cover coloring verified on {colored} graphs with cover number = matching number.")
    print(f"Type-B lattice/face comparisons and minimum-cover colorings: {bipartite} bipartite graphs.")
    for g in (cycle(4), cycle(6), Graph(6, [(a,b) for a in range(3) for b in range(3,6)])):
        a, f = normal_faces(g, True)
        print(f"n={len(g)}, edges={len(g.pairs)}, type A={lattice_gamma(g,'A')}, "
              f"type B={lattice_gamma(g,'B')}, lex complex flag={is_flag(f,len(a))}")
    a, f = normal_faces(cycle(6), True)
    assert not is_flag(f, len(a))


if __name__ == '__main__':
    main()
