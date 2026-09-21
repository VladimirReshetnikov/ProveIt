"""Exact, structurally interned finite surreal forms (Python standard library).

A node is an ordered pair of *sets of form IDs*. Equal-valued forms are NOT
merged. The stored rational value is a derived cache, not an identity key.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
from typing import Iterable


def dyadic(x: int | Fraction) -> Fraction:
    q = Fraction(x)
    if q.denominator & (q.denominator - 1):
        raise ValueError("A finite surreal value must be a dyadic rational.")
    return q


def simplest(lo: Fraction | None, hi: Fraction | None) -> Fraction:
    """The simplest dyadic strictly between lo and hi; None is unbounded.

    Search first for zero, then the nearest-to-zero eligible integer, then
    increasing denominator exponents. This is exact; there is no float use.
    """
    if lo is not None and hi is not None and lo >= hi:
        raise ValueError("Invalid cut: left bound must be strictly below right.")
    if (lo is None or lo < 0) and (hi is None or 0 < hi):
        return Fraction(0)
    if hi is not None and hi <= 0:
        return -simplest(-hi, None if lo is None else -lo)
    if lo is None:
        raise AssertionError("Unreachable interval case")
    den = 1
    while True:
        scaled = lo * den
        p = scaled.numerator // scaled.denominator + 1
        if hi is None or Fraction(p, den) < hi:
            return Fraction(p, den)
        den *= 2


@dataclass(frozen=True)
class Node:
    left: tuple[int, ...]
    right: tuple[int, ...]
    value: Fraction
    height: int


class Arena:
    """An append-only, extensional arena of valid finite number forms."""
    def __init__(self) -> None:
        self.nodes: list[Node] = []
        self.index: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
        self.make()

    def make(self, left: Iterable[int] = (), right: Iterable[int] = ()) -> int:
        L, R = tuple(sorted(set(left))), tuple(sorted(set(right)))
        if any(i < 0 or i >= len(self.nodes) for i in L + R):
            raise ValueError("Options must already exist in this arena.")
        if set(L) & set(R):
            raise ValueError("An option cannot occur on both sides of a number.")
        key = (L, R)
        if key in self.index:
            return self.index[key]
        lo = max((self.nodes[i].value for i in L), default=None)
        hi = min((self.nodes[i].value for i in R), default=None)
        value = simplest(lo, hi)
        height = 1 + max((self.nodes[i].height for i in L + R), default=-1)
        i = len(self.nodes)
        self.nodes.append(Node(L, R, value, height))
        self.index[key] = i
        return i

    def unary_left(self, i: int) -> int:
        return self.make((i,), ())

    def unary_right(self, i: int) -> int:
        return self.make((), (i,))

    def canonical(self, q: int | Fraction) -> int:
        q = dyadic(q)
        if not q:
            return 0
        if q.denominator == 1:
            i = 0
            for _ in range(abs(q.numerator)):
                i = self.unary_left(i) if q > 0 else self.unary_right(i)
            return i
        p, d = q.numerator, q.denominator
        a = self.canonical(Fraction(p - 1, d))
        b = self.canonical(Fraction(p + 1, d))
        return self.make((a,), (b,))

    def reachable(self, root: int) -> list[int]:
        seen: set[int] = set()
        stack = [root]
        while stack:
            i = stack.pop()
            if i not in seen:
                seen.add(i)
                node = self.nodes[i]
                stack.extend(node.left + node.right)
        return sorted(seen)

    def adjacency(self, root: int) -> dict[int, set[int]]:
        adj = {i: set() for i in self.reachable(root)}
        for i in adj:
            for j in self.nodes[i].left + self.nodes[i].right:
                adj[i].add(j)
                adj[j].add(i)
        return adj

    def metrics(self, root: int) -> dict:
        adj = self.adjacency(root)
        return {"value": str(self.nodes[root].value),
                "vertices": len(adj),
                "edges": sum(map(len, adj.values())) // 2,
                "height": self.nodes[root].height,
                "max_degree": max(map(len, adj.values()), default=0),
                "girth": girth(adj)}

    def certificate(self, root: int) -> dict:
        ids = self.reachable(root)
        relabel = {i: k for k, i in enumerate(ids)}
        return {"format": "finite-surreal-form-v1", "root": relabel[root],
                "nodes": [{"id": relabel[i],
                           "left": [relabel[j] for j in self.nodes[i].left],
                           "right": [relabel[j] for j in self.nodes[i].right],
                           "value": str(self.nodes[i].value),
                           "height": self.nodes[i].height}
                          for i in ids],
                "metrics": self.metrics(root)}

    def save(self, root: int, filename: str | Path) -> None:
        Path(filename).write_text(json.dumps(self.certificate(root), indent=2)
                                  + "\n", encoding="utf-8")

    def dot(self, root: int) -> str:
        lines = ['digraph form {', '  rankdir=TB;', '  node [shape=box];']
        for i in self.reachable(root):
            n = self.nodes[i]
            lines.append(f'  n{i} [label="{i}: {n.value} (h={n.height})"];')
            for j in n.left:
                lines.append(f'  n{i} -> n{j} [label="L"];')
            for j in n.right:
                lines.append(f'  n{i} -> n{j} [label="R", style=dashed];')
        return "\n".join(lines + ['}']) + "\n"


def girth(adj: dict[int, set[int]]) -> int | None:
    """Exact undirected girth by BFS; None denotes a forest (infinite girth)."""
    best: int | None = None
    for start in adj:
        dist, parent = {start: 0}, {start: None}
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v], parent[v] = dist[u] + 1, u
                    queue.append(v)
                elif parent[u] != v:
                    length = dist[u] + dist[v] + 1
                    best = length if best is None else min(best, length)
        if best == 3:
            return 3
    return best


def cycle_half(length: int) -> tuple[Arena, int]:
    """A form of 1/2 with underlying graph C_length; length=3 or >=5."""
    if length != 3 and length < 5:
        raise ValueError("Use length=3 or length>=5.")
    A = Arena()
    if length % 2:
        u = 0
        for k in range(1, length - 1):
            u = A.unary_left(u) if k % 2 else A.unary_right(u)
        root = A.make((0,), (u,))
    else:
        one = A.unary_left(0)
        minus_one = A.unary_right(0)
        minus_two = A.unary_right(minus_one)
        z = A.unary_left(minus_two)
        for _ in range((length - 6) // 2):
            z = A.unary_right(A.unary_left(z))
        root = A.make((z,), (one,))
    assert A.nodes[root].value == Fraction(1, 2)
    return A, root


# Tree nodes are ('leaf', integer) or ('cut', left_tree, right_tree).
def canonical_tree(q: int | Fraction) -> tuple:
    q = dyadic(q)
    if q.denominator == 1:
        return ('leaf', q.numerator)
    p, d = q.numerator, q.denominator
    return ('cut', canonical_tree(Fraction(p - 1, d)),
            canonical_tree(Fraction(p + 1, d)))


def leaf_labels(tree: tuple) -> list[int]:
    if tree[0] == 'leaf':
        return [tree[1]]
    return leaf_labels(tree[1]) + leaf_labels(tree[2])


def sparse_form(q: int | Fraction, minimum_girth: int = 5
                ) -> tuple[Arena, int, dict]:
    """Construct the planar, subcubic high-girth representation in the paper.

    Graph planarity follows from the ordered-tree/spine construction; the
    verifier checks exact value, distinctness, degree, size, height and girth.
    It does not use an external planarity library.
    """
    q = dyadic(q)
    if minimum_girth < 3:
        raise ValueError("minimum_girth must be at least 3.")
    A = Arena()
    if q.denominator == 1:
        root = A.canonical(q)
        return A, root, {"integer_case": True, "minimum_girth": minimum_girth}
    tree = canonical_tree(q)
    labels = leaf_labels(tree)
    gap = minimum_girth - 2
    spine, markers = [0], []
    for target in labels:
        u = spine[-1]
        v = A.nodes[u].value
        if v:
            u = A.unary_right(u) if v > 0 else A.unary_left(u)
            spine.append(u)
        for _ in range((gap + 1) // 2):
            u = A.unary_left(u)
            spine.append(u)
            u = A.unary_right(u)
            spine.append(u)
        for _ in range(abs(target)):
            u = A.unary_left(u) if target > 0 else A.unary_right(u)
            spine.append(u)
        assert A.nodes[u].value == target
        markers.append(u)
    assert len(set(spine)) == len(spine)
    it = iter(markers)
    internal = []
    def compile_tree(t: tuple) -> int:
        if t[0] == 'leaf':
            return next(it)
        left, right = compile_tree(t[1]), compile_tree(t[2])
        before = len(A.nodes)
        i = A.make((left,), (right,))
        assert len(A.nodes) == before + 1, "Unexpected structural collision"
        internal.append(i)
        return i
    root = compile_tree(tree)
    assert A.nodes[root].value == q
    L = len(labels)
    M = max(map(abs, labels))
    k = q.denominator.bit_length() - 1
    metadata = {"integer_case": False, "minimum_girth": minimum_girth,
                "gap": gap, "leaf_count": L, "max_leaf_magnitude": M,
                "denominator_exponent": k,
                "spine_vertices": len(spine), "markers": markers,
                "vertex_bound": L * (gap + M + 3),
                "height_bound": L * (gap + M + 2) + k}
    return A, root, metadata


def conway_order_table(A: Arena) -> list[list[bool]]:
    """Independent recursive Conway comparison, using structure, not values."""
    @lru_cache(None)
    def leq(x: int, y: int) -> bool:
        return (all(not leq(y, z) for z in A.nodes[x].left)
                and all(not leq(z, x) for z in A.nodes[y].right))
    return [[leq(x, y) for y in range(len(A.nodes))]
            for x in range(len(A.nodes))]


def enumerate_small(max_vertices: int = 5) -> tuple[Arena, dict[int, set[int]], int]:
    """Exhaust all finite forms with at most max_vertices distinct subforms.

    A topological labelling has sink 0 first. At vertex j each earlier vertex
    is absent, left, or right. Reject invalid cuts and duplicate form nodes;
    retain a root only when all labelled vertices are reachable from it.
    Different topological labellings are deduplicated by structural interning.
    """
    if max_vertices < 1 or max_vertices > 6:
        raise ValueError("Use 1..6; enumeration is exponential.")
    A = Arena()
    found = {n: set() for n in range(1, max_vertices + 1)}
    labelled = 0
    def visit(ids: list[int]) -> None:
        nonlocal labelled
        n, root = len(ids), ids[-1]
        if len(A.reachable(root)) == n:
            found[n].add(root)
            labelled += 1
        if n == max_vertices:
            return
        for choices in product(range(3), repeat=n):
            L = [ids[j] for j, c in enumerate(choices) if c == 1]
            R = [ids[j] for j, c in enumerate(choices) if c == 2]
            if not L and not R:
                continue
            try:
                new = A.make(L, R)
            except ValueError:
                continue
            if new not in ids:
                visit(ids + [new])
    visit([0])
    return A, found, labelled
