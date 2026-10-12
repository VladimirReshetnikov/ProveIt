"""Independent, explicitly expanded surface presentations. Validation only.

This checks the graph-of-spaces algebra, not an actual triangulated cut.
SymPy is used solely as an independent normal-form oracle in the test suite.
"""
from collections import deque
from interface_homology import Model, Core, Loop, Surface, validate


def components(n, edges):
    neighbours = [[] for _ in range(n)]
    for a, b in edges:
        neighbours[a].append(b); neighbours[b].append(a)
    labels = [-1] * n
    count = 0
    for a in range(n):
        if labels[a] != -1: continue
        labels[a] = count
        todo = [a]
        for u in todo:
            for v in neighbours[u]:
                if labels[v] == -1:
                    labels[v] = count; todo.append(v)
        count += 1
    return labels, count


def expand(model: Model, *, max_generators=2000):
    validate(model)
    core = model.core
    adjacency = [[] for _ in range(core.vertices)]
    for j, (a, b) in enumerate(core.edges):
        adjacency[a].append((b, j)); adjacency[b].append((a, j))
    visited, tree = set(), set()
    for root in range(core.vertices):
        if root in visited: continue
        visited.add(root); queue = deque([root])
        while queue:
            for v, j in adjacency[queue.popleft()]:
                if v not in visited:
                    visited.add(v); tree.add(j); queue.append(v)
    chords = [i for i in range(len(core.edges)) if i not in tree]
    ci = {a+1: j for j, a in enumerate(chords)}
    d = len(chords)
    labels, k = components(core.vertices, core.edges)
    edges = []
    nv = k
    b0_extra = 0
    surfaces = []
    estimate = d
    for s in model.surfaces:
        size = (2 if s.orientable else 1)*s.complexity + s.boundary
        estimate += size*s.multiplicity
        if estimate > max_generators or s.multiplicity > max_generators:
            raise ValueError('literal expansion allowance exceeded')
        for _ in range(s.multiplicity):
            surfaces.append(s)
            if s.attached:
                edges.extend((nv, labels[c.anchor]) for c in s.circles)
                edges.extend((nv, labels[v]) for v in s.intervals)
                nv += 1
            else:
                b0_extra += 1
    _, gc = components(nv, edges)
    graph_rank = len(edges) - nv + gc
    dim = estimate + graph_rank
    if dim > max_generators:
        raise ValueError('literal expansion allowance exceeded')
    cols = []
    def core_word(word):
        value = [0]*dim
        for x in word:
            if abs(x) in ci:
                value[ci[abs(x)]] += 1 if x > 0 else -1
        return value
    for face in core.faces:
        cols.append(core_word(face.word))
    start = d
    for s in surfaces:
        interior = (2 if s.orientable else 1)*s.complexity
        relation = [0]*dim
        if not s.orientable:
            for j in range(interior):
                relation[start+j] = 2
        for j in range(s.boundary):
            relation[start+interior+j] = 1
        cols.append(relation)
        for j, c in enumerate(s.circles):
            relation = [-x for x in core_word(c.word)]
            relation[start+interior+j] = 1
            cols.append(relation)
        start += interior+s.boundary
    matrix = tuple(tuple(col[r] for col in cols) for r in range(dim))
    return matrix, len(cols), gc+b0_extra


def sympy_smith(matrix, cols):
    from sympy import Matrix, ZZ
    from sympy.matrices.normalforms import smith_normal_form
    a = Matrix(len(matrix), cols, [x for row in matrix for x in row])
    b = smith_normal_form(a, domain=ZZ)
    return tuple(abs(int(b[i, i])) for i in range(min(b.rows, b.cols)) if b[i, i])


def random_loop(core, anchor, rng):
    adjacency = [[] for _ in range(core.vertices)]
    for j, (a, b) in enumerate(core.edges):
        adjacency[a].append((b, j+1)); adjacency[b].append((a, -j-1))
    word = []
    v = anchor
    for _ in range(rng.randrange(0, 7)):
        if not adjacency[v]: break
        v, e = rng.choice(adjacency[v]); word.append(e)
    # Independently find a shortest return path (not reversing the outward
    # walk, which would manufacture only homologically trivial examples).
    paths = {v: ()}; queue = deque([v])
    while anchor not in paths:
        u = queue.popleft()
        for w, e in adjacency[u]:
            if w not in paths:
                paths[w] = paths[u]+(e,); queue.append(w)
    return Loop(anchor, tuple(word)+paths[anchor])


def random_model(rng):
    n = rng.randrange(1, 5)
    edges = tuple((rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(0, 7)))
    core = Core(n, edges)
    core = Core(n, edges, tuple(random_loop(core, rng.randrange(n), rng) for _ in range(rng.randrange(0, 4))))
    surfaces = []
    for _ in range(rng.randrange(0, 5)):
        ori = bool(rng.randrange(2))
        g = rng.randrange(0, 3) if ori else rng.randrange(1, 4)
        b = rng.randrange(0, 4)
        c = rng.randrange(b+1)
        a = rng.randrange(0, 4) if c < b else 0
        circles = tuple(random_loop(core, rng.randrange(n), rng) for _ in range(c))
        intervals = tuple(rng.randrange(n) for _ in range(a))
        multiplicity = 1 if c or a else rng.randrange(1, 4)
        surfaces.append(Surface(ori, g, b, multiplicity, circles, intervals))
    return Model(core, tuple(surfaces))
