"""Exact finite surreal forms with structural (not value-based) interning.

Only Python's standard library is required.  Forms are finite, numerical,
well-founded pairs of sets.  Equal values never cause different forms to merge.
"""
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable

Q = Fraction


def simplest_between(lo: Q | None, hi: Q | None) -> Q:
    """The simplest dyadic strictly between finite bounds; None is infinity."""
    if lo is not None and hi is not None and lo >= hi:
        raise ValueError("The left bound must be strictly below the right bound")
    if (lo is None or lo < 0) and (hi is None or hi > 0):
        return Q(0)
    if hi is not None and hi <= 0:
        return -simplest_between(-hi, None if lo is None else -lo)
    assert lo is not None and lo >= 0
    integer = lo.numerator // lo.denominator + 1
    if hi is None or integer < hi:
        return Q(integer)
    scale = 2
    while True:
        scaled = lo * scale
        numerator = scaled.numerator // scaled.denominator + 1
        candidate = Q(numerator, scale)
        if candidate < hi:
            return candidate
        scale *= 2


def denominator_exponent(x: Q) -> int:
    denominator = x.denominator
    if denominator & (denominator - 1):
        raise ValueError("Expected a dyadic rational")
    return denominator.bit_length() - 1


def birthday(x: Q) -> int:
    x = abs(x)
    return (x.numerator + x.denominator - 1) // x.denominator + denominator_exponent(x)


@dataclass(frozen=True)
class Node:
    left: tuple[int, ...]
    right: tuple[int, ...]
    value: Q
    rank: int


class Forms:
    """An arena of hash-consed forms, addressed by integer IDs."""
    def __init__(self) -> None:
        self.nodes: list[Node] = []
        self._intern: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
        self._canonical: dict[Q, int] = {}
        self.zero = self.make((), ())

    def make(self, left: Iterable[int] = (), right: Iterable[int] = ()) -> int:
        left, right = tuple(sorted(set(left))), tuple(sorted(set(right)))
        key = (left, right)
        if key in self._intern:
            return self._intern[key]
        for child in left + right:
            if not 0 <= child < len(self.nodes):
                raise ValueError("An option must be an already constructed form")
        lo = max((self.nodes[i].value for i in left), default=None)
        hi = min((self.nodes[i].value for i in right), default=None)
        value = simplest_between(lo, hi)
        rank = max((self.nodes[i].rank + 1 for i in left + right), default=0)
        node_id = len(self.nodes)
        self.nodes.append(Node(left, right, value, rank))
        self._intern[key] = node_id
        return node_id

    def canonical(self, value: Q | int) -> int:
        x = Q(value)
        if x in self._canonical:
            return self._canonical[x]
        k = denominator_exponent(x)
        if x == 0:
            node = self.zero
        elif k == 0 and x > 0:
            node = self.make((self.canonical(x - 1),), ())
        elif k == 0:
            node = self.make((), (self.canonical(x + 1),))
        else:
            step = Q(1, x.denominator)
            node = self.make((self.canonical(x - step),),
                             (self.canonical(x + step),))
        self._canonical[x] = node
        return node

    def negate(self, root: int) -> int:
        memo: dict[int, int] = {}
        # IDs are a topological order, so no recursive call is necessary.
        for node_id in sorted(self.closure(root)):
            node = self.nodes[node_id]
            memo[node_id] = self.make((memo[i] for i in node.right),
                                      (memo[i] for i in node.left))
        return memo[root]

    def closure(self, root: int) -> set[int]:
        visited, todo = set(), [root]
        while todo:
            node_id = todo.pop()
            if node_id not in visited:
                visited.add(node_id)
                node = self.nodes[node_id]
                todo.extend(node.left + node.right)
        return visited

    def adjacency(self, root: int) -> dict[int, set[int]]:
        vertices = self.closure(root)
        graph: dict[int, set[int]] = {v: set() for v in vertices}
        for v in vertices:
            node = self.nodes[v]
            for child in node.left + node.right:
                graph[v].add(child)
                graph[child].add(v)
        return graph

    def stats(self, root: int) -> dict[str, int | str | None]:
        vertices = self.closure(root)
        edges = sum(len(self.nodes[v].left) + len(self.nodes[v].right)
                    for v in vertices)
        return {"value": str(self.nodes[root].value),
                "rank": self.nodes[root].rank, "vertices": len(vertices),
                "edges": edges, "cycle_rank": edges - len(vertices) + 1,
                "girth": girth(self.adjacency(root))}

    def certificate(self, root: int) -> dict:
        vertices = sorted(self.closure(root))
        renumber = {old: new for new, old in enumerate(vertices)}
        return {"root": renumber[root], "stats": self.stats(root), "nodes": [
            {"id": renumber[v], "left": [renumber[u] for u in self.nodes[v].left],
             "right": [renumber[u] for u in self.nodes[v].right],
             "value": str(self.nodes[v].value), "rank": self.nodes[v].rank}
            for v in vertices]}

    def odd_cycle_half(self, m: int) -> int:
        """Value 1/2, with underlying graph C_(2m+3), for m >= 1."""
        if m < 1:
            raise ValueError("m must be at least 1")
        z = self.zero
        for _ in range(m):
            negative_one = self.make((), (z,))
            z = self.make((negative_one,), ())
        one = self.canonical(1)
        return self.make((z,), (one,))

    def high_girth(self, value: Q, spacing: int) -> tuple[int, dict[str, int]]:
        """Unfold the canonical form and attach its leaves to a zero spine.

        The positive integer spacing M must satisfy 2M > b(value).
        The returned graph has girth at least 2M+2, or is acyclic.
        """
        x = Q(value)
        if spacing < 1 or 2 * spacing <= birthday(x):
            raise ValueError("Require a positive spacing M with 2M > b(x)")
        if x < 0:
            positive, meta = self.high_girth(-x, spacing)
            return self.negate(positive), meta
        if x == 0:
            return self.zero, {"leaves": 1, "internal": 0, "spacing": spacing,
                               "last_leaf_depth": 0}
        canonical_root = self.canonical(x)
        zero_spine = [self.zero]
        leaf_index = 0
        internal_count = 0
        last_leaf_depth = 0

        def zero_at(index: int) -> int:
            while len(zero_spine) <= index:
                previous = zero_spine[-1]
                negative = self.make((), (previous,))
                zero_spine.append(self.make((negative,), ()))
            return zero_spine[index]

        def unfold(node_id: int, depth: int) -> int:
            nonlocal leaf_index, internal_count, last_leaf_depth
            node = self.nodes[node_id]
            if node.value == 0:
                assert node_id == self.zero
                result = zero_at(spacing * leaf_index)
                leaf_index += 1
                last_leaf_depth = depth
                return result
            internal_count += 1
            left = [unfold(child, depth + 1) for child in node.left]
            right = [unfold(child, depth + 1) for child in node.right]
            return self.make(left, right)

        result = unfold(canonical_root, 0)
        return result, {"leaves": leaf_index, "internal": internal_count,
                        "spacing": spacing, "last_leaf_depth": last_leaf_depth}


def girth(graph: dict[int, set[int]]) -> int | None:
    """Length of a shortest undirected cycle; None means acyclic."""
    best = len(graph) + 1
    for source in graph:
        distance, parent = {source: 0}, {source: -1}
        queue = deque([source])
        while queue:
            v = queue.popleft()
            for w in graph[v]:
                if w not in distance:
                    distance[w], parent[w] = distance[v] + 1, v
                    queue.append(w)
                elif parent[v] != w:
                    best = min(best, distance[v] + distance[w] + 1)
    return best if best <= len(graph) else None


def has_subgraph(pattern: dict[int, set[int]], host: dict[int, set[int]]) -> bool:
    """Exact, non-induced, unlabelled undirected subgraph test (small graphs)."""
    if len(pattern) > len(host):
        return False
    order = sorted(pattern, key=lambda v: -len(pattern[v]))
    candidates = {v: [w for w in host if len(host[w]) >= len(pattern[v])]
                  for v in pattern}
    assigned: dict[int, int] = {}
    used: set[int] = set()

    def backtrack(position: int) -> bool:
        if position == len(order):
            return True
        v = order[position]
        for w in candidates[v]:
            if w in used:
                continue
            if any(assigned[u] not in host[w] for u in pattern[v] if u in assigned):
                continue
            assigned[v] = w
            used.add(w)
            if backtrack(position + 1):
                return True
            used.remove(w)
            del assigned[v]
        return False

    return backtrack(0)


def enumerate_forms(arena: Forms, max_vertices: int) -> list[set[int]]:
    """Exhaust all finite numerical forms with at most max_vertices vertices.

    Every finite dependency DAG has a topological ordering starting with its
    unique sink 0.  All ternary edge choices at each new vertex are examined.
    Different topological orderings are deduplicated by structural interning.
    This routine is intentionally limited to small vertex bounds.
    """
    if not 1 <= max_vertices <= 6:
        raise ValueError("Use a vertex bound from 1 to 6")
    results: list[set[int]] = [set() for _ in range(max_vertices + 1)]

    def extend(prefix: tuple[int, ...]) -> None:
        n = len(prefix)
        root = prefix[-1]
        if len(arena.closure(root)) == n:
            results[n].add(root)
        if n == max_vertices:
            return
        for choices in product(range(3), repeat=n):
            left = tuple(prefix[i] for i, side in enumerate(choices) if side == 1)
            right = tuple(prefix[i] for i, side in enumerate(choices) if side == 2)
            try:
                new = arena.make(left, right)
            except ValueError:
                continue
            if new not in prefix:
                extend(prefix + (new,))

    extend((arena.zero,))
    return results


def prefix_values(arena: Forms, x: Q) -> list[Q]:
    """Canonical sign-prefix values, from 0 to x."""
    return [arena.nodes[v].value for v in sorted(arena.closure(arena.canonical(x)),
                                               key=lambda v: arena.nodes[v].rank)]


def prefix_path(arena: Forms, root: int) -> list[int]:
    """Extract a path containing all sign-prefix values, in reverse order."""
    targets = prefix_values(arena, arena.nodes[root].value)[-2::-1]
    path, current = [root], root
    for target in targets:
        while arena.nodes[current].value != target:
            node = arena.nodes[current]
            candidates = (node.left if node.value > target else node.right)
            eligible = [v for v in candidates if
                        (target <= arena.nodes[v].value < node.value
                         if node.value > target else
                         node.value < arena.nodes[v].value <= target)]
            if not eligible:
                raise AssertionError("Prefix-path descent failed")
            current = min(eligible)
            path.append(current)
    return path
