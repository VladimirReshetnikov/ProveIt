"""Exact ordered-interface optimization of positive singleton cancellation.

Only unsigned geometric occurrence counts are valid topological inputs.
This module optimizes an abstract matrix; it does not authenticate a manifold.
Python 3.10+, standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable, Mapping


@dataclass(frozen=True)
class Edge:
    row: int
    column: int                 # global vertex id, rows first
    count: int
    allowed: bool


@dataclass(frozen=True)
class Instance:
    rows: int
    columns: int
    weights: tuple[int, ...]
    edges: tuple[Edge, ...]

    def __post_init__(self):
        if any(type(x) is not int or x < 0 for x in (self.rows, self.columns)):
            raise ValueError('invalid instance dimensions')
        if len(self.weights) != self.rows or any(type(x) is not int or x < 0 for x in self.weights):
            raise ValueError('invalid row weights')
        seen = set()
        for e in self.edges:
            if not isinstance(e, Edge) or type(e.row) is not int or type(e.column) is not int:
                raise ValueError('invalid edge')
            if not 0 <= e.row < self.rows or not self.rows <= e.column < self.vertices:
                raise ValueError('invalid edge endpoints')
            if type(e.count) is not int or e.count <= 0 or type(e.allowed) is not bool or (e.allowed and e.count != 1):
                raise ValueError('invalid edge count or pivot flag')
            if (e.row, e.column) in seen:
                raise ValueError('duplicate support edge')
            seen.add((e.row, e.column))

    @property
    def vertices(self) -> int:
        return self.rows + self.columns

    @classmethod
    def from_dense(cls, matrix: Iterable[Iterable[int]],
                   weights: Iterable[int] | None = None, *,
                   columns: int | None = None,
                   forbidden_rows: Iterable[int] = (),
                   forbidden_columns: Iterable[int] = ()) -> 'Instance':
        a = [list(row) for row in matrix]
        m = len(a)
        n = len(a[0]) if m else (0 if columns is None else columns)
        if type(n) is not int or n < 0:
            raise ValueError('invalid column count')
        if columns is not None and columns != n:
            raise ValueError('inconsistent column count')
        if any(len(row) != n for row in a):
            raise ValueError('matrix must be rectangular')
        w = tuple(1 for _ in a) if weights is None else tuple(weights)
        if len(w) != m or any(type(x) is not int or x < 0 for x in w):
            raise ValueError('weights must be nonnegative integers, one per row')
        fr, fc = set(forbidden_rows), set(forbidden_columns)
        if any(type(i) is not int or not 0 <= i < m for i in fr):
            raise ValueError('invalid forbidden row')
        if any(type(j) is not int or not 0 <= j < n for j in fc):
            raise ValueError('invalid forbidden column')
        edges = []
        for i, row in enumerate(a):
            for j, x in enumerate(row):
                if type(x) is not int or x < 0:
                    raise ValueError('counts must be unsigned integers, not signed sums')
                if x:
                    edges.append(Edge(i, m+j, x, x == 1 and i not in fr and j not in fc))
        return cls(m, n, w, tuple(edges))

    def dense(self) -> list[list[int]]:
        a = [[0] * self.columns for _ in range(self.rows)]
        for e in self.edges:
            a[e.row][e.column-self.rows] = e.count
        return a

    def to_dict(self) -> dict:
        return {'matrix': self.dense(), 'columns': self.columns,
                'weights': list(self.weights),
                'forbidden_pivots': [[e.row, e.column-self.rows]
                                     for e in self.edges if e.count == 1 and not e.allowed]}


@dataclass(frozen=True)
class Decomposition:
    """Rooted tree decomposition; edges are assigned to bags by the checker."""
    bags: tuple[frozenset[int], ...]
    parent: tuple[int | None, ...]
    root: int

    @property
    def width(self) -> int:
        return max((len(x) for x in self.bags), default=0) - 1

    def validate(self, inst: Instance) -> tuple[list[list[int]], list[list[Edge]]]:
        n = len(self.bags)
        if n == 0 or len(self.parent) != n or not 0 <= self.root < n:
            raise ValueError('invalid decomposition dimensions')
        if self.parent[self.root] is not None:
            raise ValueError('root has a parent')
        children: list[list[int]] = [[] for _ in range(n)]
        for i, p in enumerate(self.parent):
            if i == self.root:
                continue
            if type(p) is not int or not 0 <= p < n or p == i:
                raise ValueError('invalid parent')
            children[p].append(i)
        order, stack = [], [self.root]
        while stack:
            u = stack.pop()
            order.append(u)
            stack.extend(children[u])
            if len(order) > n:
                raise ValueError('parent cycle')
        if len(order) != n or len(set(order)) != n:
            raise ValueError('decomposition is not one rooted tree')
        occurrences: list[set[int]] = [set() for _ in range(inst.vertices)]
        for b, bag in enumerate(self.bags):
            for v in bag:
                if type(v) is not int or not 0 <= v < inst.vertices:
                    raise ValueError('invalid bag vertex')
                occurrences[v].add(b)
        for bags in occurrences:
            if not bags:
                raise ValueError('missing vertex')
            # In a tree, an induced subgraph is connected iff it has |V|-1 edges.
            links = sum(self.parent[b] in bags for b in bags if b != self.root)
            if links != len(bags)-1:
                raise ValueError('running-intersection property fails')
        assigned: list[list[Edge]] = [[] for _ in range(n)]
        for e in inst.edges:
            common = occurrences[e.row] & occurrences[e.column]
            if not common:
                raise ValueError('uncovered support edge')
            assigned[min(common)].append(e)
        return children, assigned


def min_fill_decomposition(inst: Instance) -> Decomposition:
    """Deterministic heuristic, not an approximation guarantee for treewidth."""
    adj = [set() for _ in range(inst.vertices)]
    for e in inst.edges:
        adj[e.row].add(e.column)
        adj[e.column].add(e.row)
    live = set(range(inst.vertices))
    eliminated, later = [], []
    while live:
        def key(v: int) -> tuple[int, int, int]:
            ns = adj[v] & live
            fill = sum(b not in adj[a] for a, b in combinations(sorted(ns), 2))
            return fill, len(ns), v
        v = min(live, key=key)
        ns = adj[v] & live
        eliminated.append(v)
        later.append(set(ns))
        for a, b in combinations(ns, 2):
            adj[a].add(b)
            adj[b].add(a)
        live.remove(v)
    pos = {v: i for i, v in enumerate(eliminated)}
    bags = [frozenset(ns | {v}) for v, ns in zip(eliminated, later)]
    root = len(bags)
    bags.append(frozenset())
    parent: list[int | None] = []
    for ns in later:
        parent.append(min((pos[x] for x in ns), default=root))
    parent.append(None)
    result = Decomposition(tuple(bags), tuple(parent), root)
    result.validate(inst)
    return result


State = tuple[tuple[int, ...], int]  # total order, matched flags in that order


@dataclass(frozen=True)
class Witness:
    kind: str
    left: 'Witness | None' = None
    right: 'Witness | None' = None
    edge: tuple[int, int] | None = None


@dataclass
class Value:
    score: int
    witness: Witness | None


class StateLimitExceeded(RuntimeError):
    """An inconclusive resource limit, never a mathematical negative result."""


def _put(table: dict[State, Value], key: State, value: Value) -> None:
    old = table.get(key)
    if old is None or value.score > old.score:
        table[key] = value


def introduce(table: dict[State, Value], vertex: int) -> dict[State, Value]:
    out: dict[State, Value] = {}
    for (order, mask), val in table.items():
        for k in range(len(order)+1):
            low = mask & ((1 << k)-1)
            shifted = low | ((mask >> k) << (k+1))
            _put(out, (order[:k]+(vertex,)+order[k:], shifted), val)
    return out


def forget(table: dict[State, Value], vertex: int) -> dict[State, Value]:
    out: dict[State, Value] = {}
    for (order, mask), val in table.items():
        k = order.index(vertex)
        shifted = (mask & ((1 << k)-1)) | ((mask >> (k+1)) << k)
        _put(out, (order[:k]+order[k+1:], shifted), val)
    return out


def introduce_edge(table: dict[State, Value], edge: Edge, weight: int) -> dict[State, Value]:
    out: dict[State, Value] = {}
    for (order, mask), val in table.items():
        i, j = order.index(edge.row), order.index(edge.column)
        if i < j:  # ordinary edge r -> c
            _put(out, (order, mask), val)
        elif edge.allowed and not (mask & ((1 << i) | (1 << j))):
            witness = Witness('edge', val.witness, edge=(edge.row, edge.column))
            _put(out, (order, mask | (1 << i) | (1 << j)), Value(val.score+weight, witness))
    return out


def join(left: dict[State, Value], right: dict[State, Value]) -> dict[State, Value]:
    out: dict[State, Value] = {}
    for (order, a), x in left.items():
        available = ((1 << len(order))-1) ^ a
        b = available
        while True:
            y = right.get((order, b))
            if y is not None:
                witness = Witness('join', x.witness, y.witness)
                _put(out, (order, a | b), Value(x.score+y.score, witness))
            if b == 0:
                break
            b = (b-1) & available
    return out


def _extract(w: Witness | None) -> list[tuple[int, int]]:
    edges, stack = [], [w]
    while stack:
        node = stack.pop()
        if node is None:
            continue
        if node.kind == 'edge':
            assert node.edge is not None
            edges.append(node.edge)
            stack.append(node.left)
        elif node.kind == 'join':
            stack.extend((node.left, node.right))
        else:
            raise AssertionError('bad internal witness node')
    return sorted(edges)


def optimize(inst: Instance, decomposition: Decomposition | None = None, *,
             state_limit: int | None = None) -> dict:
    """Return the exact optimal deferred weight and an independently replayable plan.

    The decomposition is supplied or generated by a validated min-fill heuristic.
    No claim is made that the heuristic finds minimum width.
    """
    dec = min_fill_decomposition(inst) if decomposition is None else decomposition
    children, assigned = dec.validate(inst)
    stack, preorder = [dec.root], []
    while stack:
        u = stack.pop()
        preorder.append(u)
        stack.extend(children[u])
    tables: dict[int, dict[State, Value]] = {}
    peak, transitions = 1, 0

    def observe(tab: dict[State, Value]) -> dict[State, Value]:
        nonlocal peak, transitions
        peak = max(peak, len(tab))
        transitions += len(tab)
        if state_limit is not None and len(tab) > state_limit:
            raise StateLimitExceeded(f'{len(tab)} states exceed limit {state_limit}')
        return tab

    for u in reversed(preorder):
        bag = dec.bags[u]
        table = None
        for c in children[u]:
            part = tables.pop(c)
            for v in sorted(dec.bags[c] - bag):
                part = observe(forget(part, v))
            for v in sorted(bag - dec.bags[c]):
                part = observe(introduce(part, v))
            table = part if table is None else observe(join(table, part))
        if table is None:
            table = {((), 0): Value(0, None)}
            for v in sorted(bag):
                table = observe(introduce(table, v))
        for edge in assigned[u]:
            table = observe(introduce_edge(table, edge, inst.weights[edge.row]))
        tables[u] = table
    table = tables[dec.root]
    for v in sorted(dec.bags[dec.root]):
        table = observe(forget(table, v))
    best = table[((), 0)]
    matching = _extract(best.witness)
    retained = {i for i, _ in matching}
    # The independent verifier can derive a private elimination order itself.
    result = {'schema': 'ordered-pivot-plan-v1',
              'matching': [[i, j-inst.rows] for i, j in matching],
              'deferred_rows': sorted(set(range(inst.rows))-retained),
              'retained_weight': best.score,
              'deferred_weight': sum(inst.weights)-best.score,
              'stats': {'width': dec.width, 'peak_states': peak,
                        'state_visits': transitions, 'bags': len(dec.bags)}}
    return result
