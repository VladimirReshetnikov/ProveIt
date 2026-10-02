#!/usr/bin/env python3
"""Exact, trace-free cubic certificates for finite undirected sandpiles.

Core functionality uses only the Python standard library. SymPy is needed only
for symbolic polynomial export. All certificate coordinates range over N,
including zero. This is NOT a fixed-arity universal Diophantine compiler.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Any, Iterable, Mapping, Sequence


def natural(x: Any, name: str = "value") -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be a nonnegative Python integer")
    return x


@dataclass(frozen=True)
class Graph:
    """Loopless undirected multigraph with a dissipative sink.

    a[v][w] counts internal edges; d[v] includes edges from v to the sink.
    Every internal connected component must have an edge to the sink.
    """
    a: tuple[tuple[int, ...], ...]
    d: tuple[int, ...]

    def __post_init__(self) -> None:
        n = len(self.d)
        if n == 0 or len(self.a) != n or any(len(row) != n for row in self.a):
            raise ValueError("nonempty square adjacency and matching degrees required")
        for v in range(n):
            natural(self.d[v], "degree")
            if self.d[v] == 0:
                raise ValueError("degrees must be positive")
            for w in range(n):
                natural(self.a[v][w], "edge multiplicity")
                if self.a[v][w] != self.a[w][v]:
                    raise ValueError("the proved compiler requires symmetric adjacency")
            if self.a[v][v] or self.d[v] < sum(self.a[v]):
                raise ValueError("loops or negative sink-edge multiplicities")
        unseen = set(range(n))
        while unseen:
            todo = [min(unseen)]
            component: set[int] = set()
            while todo:
                v = todo.pop()
                if v in component:
                    continue
                component.add(v)
                todo.extend(w for w in range(n) if self.a[v][w] and w not in component)
            unseen -= component
            if not any(self.d[v] > sum(self.a[v]) for v in component):
                raise ValueError("an internal component has no path to the sink")

    @property
    def n(self) -> int:
        return len(self.d)

    @property
    def edges(self) -> tuple[tuple[int, int], ...]:
        return tuple((v, w) for v in range(self.n) for w in range(self.n)
                     if self.a[v][w])

    def laplacian(self, u: Sequence[int]) -> tuple[int, ...]:
        if len(u) != self.n:
            raise ValueError("wrong vector length")
        return tuple(self.d[v]*u[v] - sum(self.a[v][w]*u[w] for w in range(self.n))
                     for v in range(self.n))


def vector(values: Sequence[int], n: int, name: str) -> tuple[int, ...]:
    if len(values) != n:
        raise ValueError(f"{name} has wrong length")
    return tuple(natural(x, name) for x in values)


def stabilize(g: Graph, eta: Sequence[int], *, bulk: bool = True,
              reverse: bool = False, max_updates: int = 2_000_000
              ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Legal serial stabilization. Limit exhaustion raises, never returns a prefix."""
    z = list(vector(eta, g.n, "eta"))
    u = [0] * g.n
    order = tuple(reversed(range(g.n))) if reverse else tuple(range(g.n))
    for _ in range(natural(max_updates, "max_updates")):
        v = next((v for v in order if z[v] >= g.d[v]), None)
        if v is None:
            return tuple(u), tuple(z)
        k = z[v] // g.d[v] if bulk else 1
        z[v] -= k*g.d[v]
        u[v] += k
        for w in range(g.n):
            z[w] += k*g.a[w][v]
    raise RuntimeError("stabilization exceeded the explicit update limit")


def stabilize_parallel(g: Graph, eta: Sequence[int], max_rounds: int = 2_000_000
                       ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Independent synchronous implementation, one toppling per unstable vertex."""
    z = list(vector(eta, g.n, "eta"))
    u = [0]*g.n
    for _ in range(natural(max_rounds, "max_rounds")):
        active = [v for v in range(g.n) if z[v] >= g.d[v]]
        if not active:
            return tuple(u), tuple(z)
        old = z[:]
        for v in range(g.n):
            z[v] = old[v] - (g.d[v] if v in active else 0)
            z[v] += sum(g.a[v][w] for w in active)
        for v in active:
            u[v] += 1
    raise RuntimeError("parallel stabilization exceeded the explicit round limit")


def burning_ranks(g: Graph, u: Sequence[int], z: Sequence[int]) -> tuple[int, ...] | None:
    u = vector(u, g.n, "u")
    z = vector(z, g.n, "z")
    remaining = {v for v in range(g.n) if u[v] > 0}
    r = [0]*g.n
    for k in range(1, g.n+1):
        if not remaining:
            return tuple(r)
        burn = {v for v in remaining if z[v] >= sum(g.a[v][w] for w in remaining)}
        if not burn:
            return None
        for v in burn:
            r[v] = k
        remaining -= burn
    return tuple(r) if not remaining else None


def local_rank_test(g: Graph, u: Sequence[int], z: Sequence[int], r: Sequence[int]) -> bool:
    if any((u[v] > 0) != (r[v] > 0) for v in range(g.n)):
        return False
    for v in range(g.n):
        if not u[v]:
            continue
        A = sum(g.a[v][w] for w in range(g.n) if r[w] >= r[v])
        B = sum(g.a[v][w] for w in range(g.n) if r[w]+1 >= r[v])
        if z[v] < A or (r[v] >= 2 and z[v] >= B):
            return False
    return True


SITE_FIELDS = ("u", "z", "ell", "r", "e", "f", "alpha", "beta", "c", "cb", "gamma", "g", "h")
EDGE_FIELDS = ("p", "pb", "s", "q", "qb", "t")


def names(g: Graph) -> tuple[str, ...]:
    return tuple(f"{field}_{v}" for v in range(g.n) for field in SITE_FIELDS) + tuple(
        f"{field}_{v}_{w}" for v, w in g.edges for field in EDGE_FIELDS)


def comparison_data(x: int, y: int) -> tuple[int, int, int]:
    return (1, 0, x-y) if x >= y else (0, 1, y-x-1)


def comparison_terms(x: Any, y: Any, b: Any, c: Any, s: Any) -> list[Any]:
    return [(b+c-1)**2, b*(x-y-s)**2, c*(y-x-1-s)**2]


def polynomial_terms(g: Graph, eta: Sequence[Any], w: Mapping[str, Any]) -> list[Any]:
    """The literal 14*n+6*m nonnegative summands (ints or symbolic expressions)."""
    def V(field: str, v: int) -> Any:
        return w[f"{field}_{v}"]
    def E(field: str, v: int, j: int) -> Any:
        return w[f"{field}_{v}_{j}"]
    result: list[Any] = []
    for v in range(g.n):
        u, z, ell, r, e, f, alpha, beta, c, cb, gamma, gg, h = (
            V(field, v) for field in SITE_FIELDS)
        A = sum(g.a[v][j]*E("p", v, j) for j in range(g.n) if g.a[v][j])
        B = sum(g.a[v][j]*E("q", v, j) for j in range(g.n) if g.a[v][j])
        balance = z+g.d[v]*u-sum(g.a[v][j]*V("u", j) for j in range(g.n))-eta[v]
        result += [balance**2, (z+ell-g.d[v]+1)**2,
                   (e+f-1)**2, e*(u-1-alpha)**2, f*(-u-alpha)**2,
                   e*(r-1-beta)**2, f*(-r-beta)**2]
        result += comparison_terms(r, 2, c, cb, gamma)
        result += [e*(z-A-gg)**2, f*gg, c*(B-z-1-h)**2, cb*h]
    for v, j in g.edges:
        result += comparison_terms(V("r", j), V("r", v),
                                   E("p", v, j), E("pb", v, j), E("s", v, j))
        result += comparison_terms(V("r", j)+1, V("r", v),
                                   E("q", v, j), E("qb", v, j), E("t", v, j))
    return result


def evaluate(g: Graph, eta: Sequence[int], witness: Mapping[str, int]) -> int:
    eta = vector(eta, g.n, "eta")
    expected = set(names(g))
    if set(witness) != expected:
        raise ValueError("missing or extra certificate coordinates")
    for name, value in witness.items():
        natural(value, name)
    return sum(polynomial_terms(g, eta, witness))


def certificate(g: Graph, eta: Sequence[int], u: Sequence[int] | None = None
                ) -> dict[str, int]:
    """Construct the canonical certificate; a supplied u is checked, not trusted."""
    eta = vector(eta, g.n, "eta")
    if u is None:
        u, z = stabilize(g, eta)
    else:
        u = vector(u, g.n, "u")
        lu = g.laplacian(u)
        z = tuple(eta[v]-lu[v] for v in range(g.n))
    if any(z[v] < 0 or z[v] >= g.d[v] for v in range(g.n)):
        raise ValueError("proposed odometer does not yield a stable nonnegative state")
    r = burning_ranks(g, u, z)
    if r is None:
        raise ValueError("proposed odometer fails support burning")
    out: dict[str, int] = {}
    for v in range(g.n):
        e, f, alpha = comparison_data(u[v], 1)
        er, fr, beta = comparison_data(r[v], 1)
        if (e, f) != (er, fr):
            raise AssertionError("support/rank mismatch")
        c, cb, gamma = comparison_data(r[v], 2)
        A = sum(g.a[v][j] for j in range(g.n) if r[j] >= r[v])
        B = sum(g.a[v][j] for j in range(g.n) if r[j]+1 >= r[v])
        gg = z[v]-A if e else 0
        h = B-z[v]-1 if c else 0
        values = (u[v], z[v], g.d[v]-1-z[v], r[v], e, f, alpha, beta,
                  c, cb, gamma, gg, h)
        out.update((f"{field}_{v}", value) for field, value in zip(SITE_FIELDS, values))
    for v, j in g.edges:
        vals = comparison_data(r[j], r[v]) + comparison_data(r[j]+1, r[v])
        out.update((f"{field}_{v}_{j}", value) for field, value in zip(EDGE_FIELDS, vals))
    if evaluate(g, eta, out) != 0:
        raise AssertionError("constructed certificate has nonzero polynomial")
    return out


def box_graph(dimension: int, radius: int) -> tuple[Graph, tuple[tuple[int, ...], ...]]:
    natural(dimension, "dimension")
    natural(radius, "radius")
    if dimension == 0:
        raise ValueError("dimension must be positive")
    sites = tuple(product(range(-radius, radius+1), repeat=dimension))
    index = {x: i for i, x in enumerate(sites)}
    a = [[0]*len(sites) for _ in sites]
    for i, x in enumerate(sites):
        for axis in range(dimension):
            for sign in (-1, 1):
                y = list(x)
                y[axis] += sign
                j = index.get(tuple(y))
                if j is not None:
                    a[i][j] += 1
    return Graph(tuple(map(tuple, a)), (2*dimension,)*len(sites)), sites


def collar_heights(sites: Sequence[tuple[int, ...]], u: Sequence[int], eta_fn: Any
                   ) -> dict[tuple[int, ...], int]:
    """Final external collar heights if only sites in the box topple."""
    inside = set(sites)
    influx: dict[tuple[int, ...], int] = {}
    dim = len(sites[0])
    for x, count in zip(sites, u):
        for axis in range(dim):
            for sign in (-1, 1):
                y = list(x)
                y[axis] += sign
                key = tuple(y)
                if key not in inside:
                    influx[key] = influx.get(key, 0) + count
    return {x: natural(eta_fn(x), "external eta")+count for x, count in influx.items()}


def symbolic_polynomial(g: Graph) -> tuple[Any, tuple[Any, ...], tuple[Any, ...]]:
    try:
        import sympy as sp
    except ImportError as exc:
        raise RuntimeError("symbolic export requires SymPy") from exc
    eta = tuple(sp.Symbol(f"eta_{v}") for v in range(g.n))
    ws = tuple(sp.Symbol(name) for name in names(g))
    expr = sp.expand(sum(polynomial_terms(g, eta, dict(zip(names(g), ws)))))
    return sp.Poly(expr, *(eta+ws), domain=sp.ZZ), eta, ws


if __name__ == "__main__":
    graph = Graph(((0, 1), (1, 0)), (2, 2))
    t = 10**100+7
    u = ((2*t-1)//3, (t-1)//3)
    cert = certificate(graph, (t, 0), u)
    print(f"natural certificate coordinates: {len(cert)}")
    print(f"nonnegative summands: {len(polynomial_terms(graph, (t, 0), cert))}")
    print(f"exact polynomial value: {evaluate(graph, (t, 0), cert)}")
    print(f"total topplings represented: {sum(u)}")
