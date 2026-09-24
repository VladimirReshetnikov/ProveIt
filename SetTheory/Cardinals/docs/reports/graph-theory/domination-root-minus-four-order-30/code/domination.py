"""Exact domination-polynomial computations. Python 3.10+, standard library only.

Polynomials are tuples of integer coefficients in ascending degree order.
Graphs are finite, simple, undirected, with vertices 0,...,n-1.
No numerical root finder or floating-point arithmetic is used.
"""
from __future__ import annotations
from collections import Counter, deque
from math import comb
from typing import Iterable

Poly = tuple[int, ...]
Edge = tuple[int, int]
ZERO: Poly = (0,)
ONE: Poly = (1,)
X: Poly = (0, 1)


def trim(a: Iterable[int]) -> Poly:
    b = list(a)
    while len(b) > 1 and b[-1] == 0:
        b.pop()
    return tuple(b) if b else ZERO


def add(a: Poly, b: Poly) -> Poly:
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        c[i] += v
    for i, v in enumerate(b):
        c[i] += v
    return trim(c)


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, tuple(-v for v in b))


def mul(a: Poly, b: Poly) -> Poly:
    c = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u:
            for j, v in enumerate(b):
                c[i + j] += u * v
    return trim(c)


def prod(polys: Iterable[Poly]) -> Poly:
    ans = ONE
    for p in polys:
        ans = mul(ans, p)
    return ans


def evaluate(p: Poly, x: int) -> int:
    ans = 0
    for v in reversed(p):
        ans = ans * x + v
    return ans


def derivative(p: Poly) -> Poly:
    return trim(i * p[i] for i in range(1, len(p)))


def divide_linear(p: Poly, root: int) -> tuple[Poly, int]:
    """Return q, r with p(x)=(x-root)q(x)+r."""
    if len(p) == 1:
        return ZERO, p[0]
    q = [0] * (len(p) - 1)
    q[-1] = p[-1]
    for i in range(len(q) - 2, -1, -1):
        q[i] = p[i + 1] + root * q[i + 1]
    return trim(q), p[0] + root * q[0]


def adjacency(n: int, edges: Iterable[Edge]) -> list[set[int]]:
    if n < 0:
        raise ValueError('Negative graph order')
    adj = [set() for _ in range(n)]
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError(f'Invalid edge {(u, v)}')
        if v in adj[u]:
            raise ValueError(f'Duplicate edge {(u, v)}')
        adj[u].add(v)
        adj[v].add(u)
    return adj


def components(adj: list[set[int]]) -> list[list[int]]:
    unseen = set(range(len(adj)))
    ans = []
    while unseen:
        todo = [min(unseen)]
        unseen.remove(todo[0])
        part = []
        while todo:
            v = todo.pop()
            part.append(v)
            for u in adj[v] & unseen:
                unseen.remove(u)
                todo.append(u)
        ans.append(sorted(part))
    return ans


def brute_polynomial(n: int, edges: Iterable[Edge]) -> Poly:
    """Direct enumeration of all 2**n vertex subsets; intended for tests."""
    adj = adjacency(n, edges)
    closed = [(1 << v) | sum(1 << u for u in adj[v]) for v in range(n)]
    ans = [0] * (n + 1)
    for selected in range(1 << n):
        if all(selected & nb for nb in closed):
            ans[selected.bit_count()] += 1
    return trim(ans)


def combine_children(children: Iterable[tuple[Poly, Poly, Poly]]) -> tuple[Poly, Poly, Poly]:
    """A=root selected; B=root dominated, absent; C=root undominated, absent."""
    children = tuple(children)
    total = prod(add(add(a, b), c) for a, b, c in children)
    dominated = prod(add(a, b) for a, b, _ in children)
    absent = prod(b for _, b, _ in children)
    return mul(X, total), sub(dominated, absent), absent


def rooted_polynomials(shape: tuple) -> tuple[Poly, Poly, Poly]:
    """A rooted-tree shape is the tuple of the shapes of its children."""
    return combine_children(rooted_polynomials(child) for child in shape)


def core_polynomial(n: int, edges: Iterable[Edge]) -> tuple[Poly, list[int]]:
    """Strip pendant trees; enumerate selected subsets of the remaining 2-core.

    Exact for arbitrary graphs, including disconnected graphs and empty cores.
    Exponential only in the number of surviving core vertices, not necessarily n.
    """
    adj = adjacency(n, edges)
    active = [True] * n
    queue = deque(v for v in range(n) if len(adj[v]) < 2)
    total = [ONE] * n
    dominated = [ONE] * n
    absent = [ONE] * n
    forest_factor = ONE
    while queue:
        v = queue.popleft()
        if not active[v] or len(adj[v]) >= 2:
            continue
        a = mul(X, total[v])
        b = sub(dominated[v], absent[v])
        c = absent[v]
        active[v] = False
        if not adj[v]:
            forest_factor = mul(forest_factor, add(a, b))
        else:
            u = next(iter(adj[v]))
            adj[u].remove(v)
            adj[v].clear()
            total[u] = mul(total[u], add(add(a, b), c))
            dominated[u] = mul(dominated[u], add(a, b))
            absent[u] = mul(absent[u], b)
            if len(adj[u]) < 2:
                queue.append(u)
    core = [v for v in range(n) if active[v]]
    pos = {v: i for i, v in enumerate(core)}
    masks = [sum(1 << pos[u] for u in adj[v]) for v in core]
    core_sum = ZERO
    for selected in range(1 << len(core)):
        term = ONE
        for i, v in enumerate(core):
            if selected & (1 << i):
                factor = mul(X, total[v])
            elif selected & masks[i]:
                factor = dominated[v]  # B+C: root is dominated from the core.
            else:
                factor = sub(dominated[v], absent[v])  # B only.
            term = mul(term, factor)
        core_sum = add(core_sum, term)
    return mul(forest_factor, core_sum), core


def leaf_terms(n: int, edges: Iterable[Edge]) -> Counter[tuple[int, int]]:
    """Return m[a,b] for D=sum m[a,b] x**a (1+x)**b.

    Requires no component isomorphic to K2. Isolated vertices are allowed.
    This algorithm does not use rooted states or 2-core stripping.
    """
    adj = adjacency(n, edges)
    if any(len(adj[v]) == len(adj[u]) == 1 for v in range(n) for u in adj[v]):
        raise ValueError('Use leaf_polynomial for graphs with K2 components')
    leaves = {v for v in range(n) if len(adj[v]) == 1}
    core = [v for v in range(n) if v not in leaves]
    pos = {v: i for i, v in enumerate(core)}
    tails = [len(adj[v] & leaves) for v in core]
    closed = [(1 << i) | sum(1 << pos[u] for u in adj[v] if u in pos)
              for i, v in enumerate(core)]
    required = [closed[i] for i, t in enumerate(tails) if t == 0]
    ans: Counter[tuple[int, int]] = Counter()
    for selected in range(1 << len(core)):
        if not all(selected & nb for nb in required):
            continue
        optional = sum(t for i, t in enumerate(tails) if selected & (1 << i))
        forced = len(leaves) - optional
        ans[selected.bit_count() + forced, optional] += 1
    return ans


def expand_leaf_terms(terms: Counter[tuple[int, int]]) -> Poly:
    ans = [0]
    for (a, b), multiplicity in terms.items():
        if len(ans) <= a + b:
            ans.extend([0] * (a + b + 1 - len(ans)))
        for j in range(b + 1):
            ans[a + j] += multiplicity * comb(b, j)
    return trim(ans)


def leaf_polynomial(n: int, edges: Iterable[Edge]) -> Poly:
    """Leaf-subset enumeration, with K2 components removed first."""
    edges = tuple(edges)
    adj = adjacency(n, edges)
    remove = {v for v in range(n) if len(adj[v]) == 1
              and len(adj[next(iter(adj[v]))]) == 1}
    if not remove:
        return expand_leaf_terms(leaf_terms(n, edges))
    vertices = [v for v in range(n) if v not in remove]
    pos = {v: i for i, v in enumerate(vertices)}
    reduced_edges = [(pos[u], pos[v]) for u, v in edges if u in pos and v in pos]
    return mul(prod([(0, 2, 1)] * (len(remove) // 2)),
               expand_leaf_terms(leaf_terms(len(vertices), reduced_edges)))


def construction_shapes() -> dict[str, tuple]:
    leaf = ()
    edge = (leaf,)
    path3 = (edge,)
    star3 = (leaf,) * 3
    central = (edge, edge, edge, star3)
    return {'L': leaf, 'E': edge, 'J': path3, 'S3': star3,
            'W': central, 'T': (leaf, central), 'K': (leaf, path3),
            'S5': (leaf,) * 5}


def four_cycle_certificate() -> Poly:
    """A third polynomial expression from the paper's inclusion-exclusion identity."""
    states = {name: rooted_polynomials(shape)
              for name, shape in construction_shapes().items()}
    ae, be, _ = states['E']
    at, bt, _ = states['T']
    ak, bk, _ = states['K']
    ar, br, _ = states['S5']
    pe, pt, pk, pr = add(ae, be), add(at, bt), add(ak, bk), add(ar, br)
    main = prod([(3, 6, 4, 1), pe, pt, pk, pr])
    shared_hub = prod([br, pk, add(mul(be, pt), mul(bt, pe))])
    last_site = prod([bk, pe, pt, pr])
    return mul(X, sub(sub(main, shared_hub), last_site))
