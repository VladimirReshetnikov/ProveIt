"""Cographic batch selection; graph-level certificates, NOT a knot recognizer.

Edges are oriented from negative to positive side.  A valid geometric caller
must authenticate connected, pairwise disjoint, two-sided candidate surfaces
and the source-to-chamber census.  This module does not do that authentication.
Only the standard library is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from typing import Iterable, Sequence


class InvalidInput(ValueError):
    pass


def integer(x: object, name: str, minimum: int = 0) -> int:
    if type(x) is not int or x < minimum:
        raise InvalidInput(f"{name} must be an integer >= {minimum}")
    return x


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n
        self.count = n

    def find(self, x: int) -> int:
        while x != self.parent[x]:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> bool:
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.size[a] += self.size[b]
        self.count -= 1
        return True


@dataclass(frozen=True)
class Graph:
    vertices: int
    edges: tuple[tuple[int, int], ...]
    weights: tuple[int, ...]

    def __post_init__(self) -> None:
        integer(self.vertices, "vertices", 1)
        if self.vertices > len(self.edges) + 1:
            raise InvalidInput("too many vertices for a connected graph")
        if len(self.weights) != len(self.edges):
            raise InvalidInput("one weight per edge required")
        d = DSU(self.vertices)
        for i, (a, b) in enumerate(self.edges):
            integer(a, "endpoint")
            integer(b, "endpoint")
            if max(a, b) >= self.vertices:
                raise InvalidInput("endpoint out of range")
            integer(self.weights[i], "weight")
            d.union(a, b)
        if d.count != 1:
            raise InvalidInput("chamber graph must be connected")

    def packet(self) -> dict:
        return {"vertices": self.vertices, "edges": [list(e) for e in self.edges],
                "weights": list(self.weights)}


def decode_side_census(k: int, histogram: Iterable[tuple[int, int]],
                       weights: Sequence[int] | None = None) -> Graph:
    """Decode (orbit weight, orbit multiplicity) rows of one scalar census.

    Marker 2*i is the negative side of surface i; marker 2*i+1 is positive.
    Each marker has weight 2**marker and occurs exactly once in the source.
    For k>0 every actual chamber must have at least one marker.  Nonzero masks
    therefore occur with multiplicity one.  k=0 has the special row (0,1).
    This checks the census's algebraic consistency, not its source truth.
    """
    integer(k, "k")
    rows = tuple(histogram)
    if k == 0:
        if rows != ((0, 1),):
            raise InvalidInput("empty surface system requires one empty chamber")
        if weights is not None and len(weights) != 0:
            raise InvalidInput("wrong weight count")
        return Graph(1, (), ())
    if not rows or len(rows) > k + 1:
        raise InvalidInput("invalid number of chambers")
    seen = 0
    masks = []
    for mask, multiplicity in rows:
        integer(mask, "mask", 1)
        integer(multiplicity, "multiplicity", 1)
        if multiplicity != 1 or mask.bit_length() > 2*k or seen & mask:
            raise InvalidInput("repeated, out-of-range, or aliased marker")
        masks.append(mask)
        seen |= mask
    if seen.bit_length() != 2*k or seen.bit_count() != 2*k:
        raise InvalidInput("missing side marker")
    masks.sort(key=lambda m: (m & -m).bit_length())
    locations = [-1] * (2 * k)
    for chamber, mask in enumerate(masks):
        while mask:
            bit = mask & -mask
            locations[bit.bit_length() - 1] = chamber
            mask -= bit
    return Graph(len(rows), tuple((locations[2*i], locations[2*i+1]) for i in range(k)),
                 tuple([1] * k if weights is None else weights))


def side_histogram(graph: Graph) -> tuple[tuple[int, int], ...]:
    if not graph.edges:
        return ((0, 1),)
    masks = [0] * graph.vertices
    for i, (u, v) in enumerate(graph.edges):
        masks[u] += 1 << (2*i)
        masks[v] += 1 << (2*i+1)
    return tuple((m, 1) for m in masks)


def maximum_batch(graph: Graph) -> dict:
    """Complement of a minimum-weight spanning tree; linear-size certificate."""
    d = DSU(graph.vertices)
    tree = []
    for e in sorted(range(len(graph.edges)), key=lambda i: (graph.weights[i], i)):
        if d.union(*graph.edges[e]):
            tree.append(e)
    tree.sort()
    keep = set(tree)
    chosen = [e for e in range(len(graph.edges)) if e not in keep]
    return {"schema": "cographic-batch-v1", "graph": graph.packet(),
            "tree": tree, "chosen": chosen,
            "reward": sum(graph.weights[e] for e in chosen),
            "scope": "relative-to-authenticated-chamber-graph"}


def components_after_cut(graph: Graph, chosen: Iterable[int]) -> int:
    chosen = set(chosen)
    for e in chosen:
        integer(e, "chosen edge")
        if e >= len(graph.edges):
            raise InvalidInput("chosen edge out of range")
    d = DSU(graph.vertices)
    for e, (a, b) in enumerate(graph.edges):
        if e not in chosen:
            d.union(a, b)
    return d.count


def tree_return(graph: Graph, tree: Sequence[int], e: int) -> tuple[tuple[int, int], ...]:
    """Signed fundamental cycle: first traverse e forward, then tree back.

    Literal path expansion is an optional finite witness/debug operation.
    The compact certificate stores the tree and chord, not all expanded paths.
    """
    integer(e, "chord")
    if e >= len(graph.edges) or e in tree:
        raise InvalidInput("not a chord")
    adj = [[] for _ in range(graph.vertices)]
    for t in tree:
        u, v = graph.edges[t]
        adj[u].append((v, t, 1))
        adj[v].append((u, t, -1))
    u, v = graph.edges[e]
    todo = deque([v]); back = {v: None}
    while todo and u not in back:
        x = todo.popleft()
        for y, t, sign in adj[x]:
            if y not in back:
                back[y] = (x, t, sign)
                todo.append(y)
    if u not in back:
        raise InvalidInput("tree does not provide return path")
    path = []
    x = u
    while x != v:
        prev, t, sign = back[x]
        path.append((t, sign))
        x = prev
    return ((e, 1),) + tuple(reversed(path))


def finite_routing_forest(atom_count: int, interior: Sequence[tuple[int, int]],
                          gates: Sequence[tuple[int, int]],
                          weights: Sequence[int] | None = None) -> dict:
    """Finite source-arena lift.  Not a compressed native geometry exporter.

    Interior edges join source cells without crossing a candidate surface.
    Exactly one signed gate represents each connected cooriented surface.
    Source charts must independently justify those interpretations.
    A forest inside each chamber, plus the selected chamber-tree gates, is a
    single spanning tree of the source arena. Chord gates encode all dual loops.
    """
    integer(atom_count, "atom_count", 1)
    if atom_count > len(interior) + len(gates) + 1:
        raise InvalidInput("too few edges for a connected source arena")
    for a, b in tuple(interior) + tuple(gates):
        if type(a) is not int or type(b) is not int or min(a, b) < 0 or max(a, b) >= atom_count:
            raise InvalidInput("source endpoint out of range")
    d = DSU(atom_count)
    forest = []
    for i, (a, b) in enumerate(interior):
        if d.union(a, b):
            forest.append(i)
    roots = sorted({d.find(a) for a in range(atom_count)})
    index = {r: i for i, r in enumerate(roots)}
    g = Graph(len(roots), tuple((index[d.find(a)], index[d.find(b)]) for a, b in gates),
              tuple([1]*len(gates) if weights is None else weights))
    batch = maximum_batch(g)
    for i in batch['tree']:
        if not d.union(*gates[i]):
            raise AssertionError("chamber tree lift contains a cycle")
    if d.count != 1:
        raise AssertionError("routing forest is not connected")
    return {"schema": "finite-routing-forest-v1", "atom_count": atom_count,
            "interior": [list(e) for e in interior], "gates": [list(e) for e in gates],
            "forest": forest, "batch": batch}
