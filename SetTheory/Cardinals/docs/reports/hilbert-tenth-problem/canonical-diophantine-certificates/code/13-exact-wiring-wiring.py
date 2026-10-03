"""Exact interaction-combinator wiring, with cyclic components retained.

Only the Python standard library is required.  The sequential splice evaluator
and the component evaluator deliberately use different algorithms.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable, Iterator

Edge = tuple[int, int]
Matching = tuple[Edge, ...]
ARITY = {"epsilon": 0, "delta": 2, "gamma": 2}


def natural(x: int, name: str = "value") -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be an exact nonnegative Python integer")
    return x


def matchings(points: Iterable[int]) -> Iterator[Matching]:
    p = tuple(sorted(points))
    if len(set(p)) != len(p) or len(p) % 2:
        raise ValueError("an even number of distinct endpoints is required")
    if not p:
        yield ()
        return
    a = p[0]
    for i in range(1, len(p)):
        for rest in matchings(p[1:i] + p[i + 1:]):
            yield tuple(sorted(((a, p[i]),) + rest))


def involution(edges: Iterable[Edge]) -> dict[int, int]:
    ans: dict[int, int] = {}
    for a, b in edges:
        if type(a) is not int or type(b) is not int or a == b or a in ans or b in ans:
            raise ValueError("edges must be disjoint pairs of distinct integer ports")
        ans[a], ans[b] = b, a
    return ans


def edges_of(mate: dict[int, int]) -> Matching:
    for a, b in mate.items():
        if a == b or mate.get(b) != a:
            raise ValueError("not a fixed-point-free involution")
    return tuple(sorted((a, b) for a, b in mate.items() if a < b))


def union_components(m: Matching, n: Matching) -> list[set[int]]:
    a, b = involution(m), involution(n)
    if a.keys() != b.keys():
        raise ValueError("matching domains differ")
    left = set(a)
    result: list[set[int]] = []
    while left:
        pending, component = [min(left)], set()
        while pending:
            x = pending.pop()
            if x in component:
                continue
            component.add(x)
            pending.extend((a[x], b[x]))
        left.difference_update(component)
        result.append(component)
    return result


def closure_loops(m: Matching, n: Matching) -> int:
    # A double edge is a genuine two-edge component.
    return len(union_components(m, n))


def switch_context(m: Matching, n: Matching, modulus: int = 2) -> Matching:
    """Construct a closing context distinguishing loop counts modulo modulus.

    The context is m itself or differs from m in exactly two edges.
    """
    natural(modulus, "modulus")
    if modulus < 2 or m == n:
        raise ValueError("need modulus >= 2 and distinct matchings")
    c = closure_loops(m, n)
    rank = len(m)
    if (rank - c) % modulus:
        return m
    comp = next(z for z in union_components(m, n) if len(z) >= 4)
    e, f = [e for e in m if e[0] in comp][:2]
    a, b = e
    c0, d = f
    rest = tuple(e0 for e0 in m if e0 != e and e0 != f)
    alternatives = [((a, c0), (b, d)), ((a, d), (b, c0))]
    for new in alternatives:
        q = tuple(sorted(rest + tuple(tuple(sorted(e0)) for e0 in new)))
        if closure_loops(n, q) == c:
            assert closure_loops(m, q) == rank - 1
            assert (closure_loops(m, q) - closure_loops(n, q)) % modulus
            return q
    raise AssertionError("the nonsplitting switch must exist")


def splice(mate: dict[int, int], a: int, b: int) -> int:
    """Suppress a,b after adding a join, mutating mate; return new loop count."""
    if a == b or a not in mate or b not in mate:
        raise ValueError("splice requires two distinct live ports")
    p, q = mate[a], mate[b]
    if p == b:
        if q != a:
            raise ValueError("asymmetric matching")
        del mate[a], mate[b]
        return 1
    if p == q or p in (a, b) or q in (a, b) or mate[p] != a or mate[q] != b:
        raise ValueError("invalid splice neighborhood")
    del mate[a], mate[b]
    mate[p], mate[q] = q, p
    return 0


def component_glue(mate: dict[int, int], joins: list[Edge]) -> tuple[dict[int, int], int]:
    """Independent multigraph implementation. Parallel edges are not deduplicated."""
    graph = {x: [] for x in mate}
    for a, b in edges_of(mate) + tuple(joins):
        graph[a].append(b)
        graph[b].append(a)
    deleted = {x for e in joins for x in e}
    if len(deleted) != 2 * len(joins):
        raise ValueError("join endpoints must be distinct")
    for x, adj in graph.items():
        if len(adj) != (2 if x in deleted else 1):
            raise ValueError("invalid degree in gluing graph")
    left, out, loops = set(graph), {}, 0
    while left:
        todo, comp = [min(left)], set()
        while todo:
            x = todo.pop()
            if x in comp:
                continue
            comp.add(x)
            todo.extend(graph[x])
        left.difference_update(comp)
        end = sorted(comp - deleted)
        if not end:
            loops += 1
        elif len(end) == 2:
            a, b = end
            out[a], out[b] = b, a
        else:
            raise AssertionError("a component must be a path or a cycle")
    return out, loops


def port(c: int, p: int) -> int:
    return 3 * c + p + 1


@dataclass(frozen=True)
class Layout:
    initial_cells: int
    horizon: int
    free_count: int = 0

    def __post_init__(self) -> None:
        natural(self.initial_cells, "initial_cells")
        natural(self.horizon, "horizon")
        natural(self.free_count, "free_count")

    @property
    def capacity(self) -> int:
        return self.initial_cells + 4 * self.horizon

    @property
    def free_ports(self) -> tuple[int, ...]:
        return tuple(3 * self.capacity + i + 1 for i in range(self.free_count))

    def boundary(self, step: int, i: int) -> int:
        return 3 * self.capacity + self.free_count + 4 * step + i + 1


@dataclass
class Net:
    cells: dict[int, str]
    mate: dict[int, int]
    loops: int = 0
    free: tuple[int, ...] = ()

    def validate(self) -> None:
        natural(self.loops, "loops")
        domain = set(self.free)
        if len(domain) != len(self.free):
            raise ValueError("repeated free endpoint")
        for c, label in self.cells.items():
            natural(c, "cell")
            if label not in ARITY:
                raise ValueError("unknown agent")
            ps = {port(c, p) for p in range(ARITY[label] + 1)}
            if domain.intersection(ps):
                raise ValueError("overlapping port allocations")
            domain.update(ps)
        if domain != set(self.mate):
            raise ValueError("port domain does not match agents and interface")
        edges_of(self.mate)

    def active_pairs(self) -> list[tuple[int, int]]:
        ans = []
        for c in sorted(self.cells):
            q = self.mate[port(c, 0)]
            if (q - 1) % 3 == 0:
                d = (q - 1) // 3
                if d in self.cells and c < d:
                    ans.append((c, d))
        return ans

    def record(self) -> dict:
        return {"cells": sorted(self.cells.items()), "wires": edges_of(self.mate),
                "loops": self.loops, "free": self.free}


def rhs(net: Net, u: int, v: int, step: int, layout: Layout):
    """Literal six-rule table with Lafont's numbered auxiliary-port convention."""
    if not 0 <= step < layout.horizon or not u < v:
        raise ValueError("invalid step or orientation")
    if net.mate.get(port(u, 0)) != port(v, 0):
        raise ValueError("not an active principal pair")
    a, b = net.cells[u], net.cells[v]
    old = [port(c, p) for c in (u, v) for p in range(1, ARITY[net.cells[c]] + 1)]
    boundary = {x: layout.boundary(step, i) for i, x in enumerate(old)}
    fresh = [layout.initial_cells + 4 * step + j for j in range(4)]
    new: dict[int, str] = {}
    wiring: list[Edge] = []
    if a == b:
        if a != "epsilon":
            order = (1, 2) if a == "delta" else (2, 1)
            wiring = [(boundary[port(u, i)], boundary[port(v, j)])
                      for i, j in zip((1, 2), order)]
    elif "epsilon" in (a, b):
        binary = v if a == "epsilon" else u
        new = {fresh[0]: "epsilon", fresh[1]: "epsilon"}
        wiring = [(boundary[port(binary, i)], port(fresh[i - 1], 0)) for i in (1, 2)]
    else:
        d, g = (u, v) if a == "delta" else (v, u)
        gs, ds = fresh[:2], fresh[2:]
        new = {**{x: "gamma" for x in gs}, **{x: "delta" for x in ds}}
        wiring = [(boundary[port(d, i)], port(gs[i - 1], 0)) for i in (1, 2)]
        wiring += [(boundary[port(g, j)], port(ds[j - 1], 0)) for j in (1, 2)]
        wiring += [(port(gs[i - 1], j), port(ds[j - 1], i))
                   for i in (1, 2) for j in (1, 2)]
    return new, involution(wiring), [(x, boundary[x]) for x in old]


def rewrite(net: Net, u: int, v: int, step: int, layout: Layout,
            method: str = "splice", join_order: tuple[int, ...] | None = None) -> Net:
    net.validate()
    new, right, joins = rhs(net, u, v, step, layout)
    if set(new).intersection(net.cells):
        raise ValueError("fresh cells already live")
    mate = {x: y for x, y in net.mate.items() if x not in (port(u, 0), port(v, 0))}
    if set(mate).intersection(right):
        raise ValueError("RHS port allocation is not fresh")
    mate.update(right)
    if method == "components":
        mate, inc = component_glue(mate, joins)
    elif method == "splice":
        order = tuple(range(len(joins))) if join_order is None else join_order
        if sorted(order) != list(range(len(joins))):
            raise ValueError("not a permutation of interface joins")
        inc = sum(splice(mate, *joins[i]) for i in order)
    else:
        raise ValueError("unknown reduction method")
    cells = {c: t for c, t in net.cells.items() if c not in (u, v)}
    cells.update(new)
    ans = Net(cells, mate, net.loops + inc, net.free)
    ans.validate()
    return ans
