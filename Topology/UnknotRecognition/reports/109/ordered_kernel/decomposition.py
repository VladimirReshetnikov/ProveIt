"""Supplied tree decompositions and a deterministic min-fill heuristic.

The heuristic gives a certified width, not the optimal treewidth. An optional
elimination order enables source-specific decompositions without a search.
"""
from dataclasses import dataclass
from .model import Check, noop

@dataclass
class Decomposition:
    bags: list[tuple[int, ...]]
    parent: list[int | None]

    @property
    def width(self) -> int:
        return max((len(b) - 1 for b in self.bags), default=-1)

    def to_dict(self) -> dict:
        return {'bags': [list(b) for b in self.bags], 'parent': self.parent}

    @classmethod
    def from_dict(cls, obj: dict) -> 'Decomposition':
        if type(obj) is not dict or set(obj) != {'bags', 'parent'}:
            raise ValueError('invalid decomposition object')
        return cls([tuple(b) for b in obj['bags']], list(obj['parent']))


def validate(td: Decomposition, adj: list[set[int]]) -> tuple[int, list[list[int]], list[int]]:
    n, q = len(adj), len(td.bags)
    if not q or len(td.parent) != q:
        raise ValueError('decomposition must have a nonempty bag tree')
    roots = [i for i, p in enumerate(td.parent) if p is None]
    if len(roots) != 1:
        raise ValueError('exactly one root is required')
    children = [[] for _ in range(q)]
    for i, p in enumerate(td.parent):
        if p is not None:
            if type(p) is not int or not 0 <= p < q or p == i:
                raise ValueError('invalid parent')
            children[p].append(i)
    root = roots[0]
    order, stack, seen = [], [root], set()
    while stack:
        i = stack.pop()
        if i in seen:
            raise ValueError('parent relation contains a cycle')
        seen.add(i); order.append(i); stack.extend(children[i])
    if len(seen) != q:
        raise ValueError('parent relation is not a tree')
    occurs = [set() for _ in range(n)]
    for i, bag in enumerate(td.bags):
        if len(set(bag)) != len(bag):
            raise ValueError('duplicate vertex in bag')
        for v in bag:
            if type(v) is not int or not 0 <= v < n:
                raise ValueError('invalid graph vertex in bag')
            occurs[v].add(i)
    for v, bags in enumerate(occurs):
        if not bags:
            raise ValueError('graph vertex is uncovered')
        # A subset of vertices of a tree is connected iff induced edge count
        # is its cardinality minus one.
        induced = sum(td.parent[i] in bags for i in bags)
        if induced != len(bags) - 1:
            raise ValueError('running-intersection property fails')
        for w in adj[v]:
            if v < w and not bags.intersection(occurs[w]):
                raise ValueError('graph edge is uncovered')
    return root, children, order


def elimination_decomposition(adj: list[set[int]], order: list[int] | None = None,
                              *, check: Check = noop) -> Decomposition:
    n = len(adj)
    if order is not None and (len(order) != n or set(order) != set(range(n))
                              or any(type(x) is not int for x in order)):
        raise ValueError('elimination order must be a vertex permutation')
    graph = [set(x) for x in adj]
    live = set(range(n)); elim = []; bags = []
    for step in range(n):
        check()
        if order is None:
            def score(v):
                nei = sorted(graph[v])
                missing = sum(b not in graph[a] for i, a in enumerate(nei) for b in nei[i+1:])
                return missing, len(nei), v
            v = min(live, key=score)
        else:
            v = order[step]
        nei = sorted(graph[v])
        bags.append(tuple([v] + nei)); elim.append(v)
        for i, a in enumerate(nei):
            graph[a].discard(v)
            for b in nei[i+1:]:
                graph[a].add(b); graph[b].add(a)
        graph[v].clear(); live.remove(v)
    position = {v: i for i, v in enumerate(elim)}
    parent = [min((position[w] for w in bag[1:]), default=n) for bag in bags]
    bags.append(()); parent.append(None)
    td = Decomposition(bags, parent)
    validate(td, adj)
    return td
