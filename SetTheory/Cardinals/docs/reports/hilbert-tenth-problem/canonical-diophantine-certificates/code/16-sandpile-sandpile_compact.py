#!/usr/bin/env python3
"""Compact cubic compiler: 10 vertex variables and 6 per undirected adjacency.

The derived rank is k+2*c+beta. For an edge v<w a five-way selector
classifies rank[w]-rank[v] as <=-2, -1, 0, 1, or >=2. Natural zeros are
in explicit bijection with the baseline compiler's natural zeros.
"""
from __future__ import annotations
from typing import Any, Mapping, Sequence
from sandpile_cubic import Graph, vector, natural, stabilize, burning_ranks

SITE_FIELDS = ("u", "z", "ell", "f", "k", "c", "alpha", "beta", "g", "h")
EDGE_FIELDS = ("lo", "neg", "eq", "pos", "hi", "gap")


def edges(g: Graph) -> tuple[tuple[int, int], ...]:
    return tuple((v, j) for v, j in g.edges if v < j)


def names(g: Graph) -> tuple[str, ...]:
    return tuple(f"{f}_{v}" for v in range(g.n) for f in SITE_FIELDS) + tuple(
        f"{f}_{v}_{j}" for v, j in edges(g) for f in EDGE_FIELDS)


def five_data(delta: int) -> tuple[int, int, int, int, int, int]:
    if delta <= -2:
        return 1, 0, 0, 0, 0, -delta-2
    if delta == -1:
        return 0, 1, 0, 0, 0, 0
    if delta == 0:
        return 0, 0, 1, 0, 0, 0
    if delta == 1:
        return 0, 0, 0, 1, 0, 0
    return 0, 0, 0, 0, 1, delta-2


def five_terms(delta: Any, lo: Any, neg: Any, eq: Any, pos: Any,
               hi: Any, gap: Any) -> list[Any]:
    return [(lo+neg+eq+pos+hi-1)**2,
            lo*(delta+2+gap)**2, neg*(delta+1)**2, eq*delta**2,
            pos*(delta-1)**2, hi*(delta-2-gap)**2, (neg+eq+pos)*gap]


def polynomial_terms(g: Graph, eta: Sequence[Any], w: Mapping[str, Any]) -> list[Any]:
    r = [w[f"k_{v}"]+2*w[f"c_{v}"]+w[f"beta_{v}"] for v in range(g.n)]
    A: list[Any] = [0]*g.n
    B: list[Any] = [0]*g.n
    edge_terms: list[Any] = []
    for v, j in edges(g):
        lo, neg, eq, pos, hi, gap = (w[f"{f}_{v}_{j}"] for f in EDGE_FIELDS)
        a = g.a[v][j]
        A[v] += a*(eq+pos+hi)
        B[v] += a*(neg+eq+pos+hi)
        A[j] += a*(lo+neg+eq)
        B[j] += a*(lo+neg+eq+pos)
        edge_terms += five_terms(r[j]-r[v], lo, neg, eq, pos, hi, gap)
    result: list[Any] = []
    for v in range(g.n):
        u, z, ell, f, k, c, alpha, beta, gg, h = (w[f"{field}_{v}"] for field in SITE_FIELDS)
        balance = z+g.d[v]*u-sum(g.a[v][j]*w[f"u_{j}"] for j in range(g.n))-eta[v]
        result += [balance**2, (z+ell-g.d[v]+1)**2, (f+k+c-1)**2,
                   (u-k-c-alpha)**2, f*alpha, (f+k)*beta,
                   (k+c)*(z-A[v]-gg)**2, f*gg,
                   c*(B[v]-z-1-h)**2, (f+k)*h]
    return result+edge_terms


def evaluate(g: Graph, eta: Sequence[int], w: Mapping[str, int]) -> int:
    eta = vector(eta, g.n, "eta")
    if set(w) != set(names(g)):
        raise ValueError("missing or extra compact certificate coordinates")
    for name, value in w.items():
        natural(value, name)
    return sum(polynomial_terms(g, eta, w))


def certificate(g: Graph, eta: Sequence[int], u: Sequence[int] | None = None) -> dict[str, int]:
    eta = vector(eta, g.n, "eta")
    if u is None:
        u, z = stabilize(g, eta)
    else:
        u = vector(u, g.n, "u")
        lu = g.laplacian(u)
        z = tuple(eta[v]-lu[v] for v in range(g.n))
    if any(not 0 <= z[v] < g.d[v] for v in range(g.n)):
        raise ValueError("unstable or negative candidate endpoint")
    r = burning_ranks(g, u, z)
    if r is None:
        raise ValueError("candidate fails support burning")
    out: dict[str, int] = {}
    for v in range(g.n):
        f, k, c = int(r[v] == 0), int(r[v] == 1), int(r[v] >= 2)
        A = sum(g.a[v][j] for j in range(g.n) if r[j] >= r[v])
        B = sum(g.a[v][j] for j in range(g.n) if r[j]+1 >= r[v])
        vals = (u[v], z[v], g.d[v]-1-z[v], f, k, c,
                u[v]-1 if u[v] else 0, r[v]-2 if c else 0,
                z[v]-A if not f else 0, B-z[v]-1 if c else 0)
        out.update((f"{field}_{v}", val) for field, val in zip(SITE_FIELDS, vals))
    for v, j in edges(g):
        vals = five_data(r[j]-r[v])
        out.update((f"{field}_{v}_{j}", val) for field, val in zip(EDGE_FIELDS, vals))
    if evaluate(g, eta, out) != 0:
        raise AssertionError("compact certificate is nonzero")
    return out


def from_baseline(g: Graph, eta: Sequence[int], old: Mapping[str, int]) -> dict[str, int]:
    from sandpile_cubic import evaluate as baseline_evaluate
    if baseline_evaluate(g, eta, old) != 0:
        raise ValueError("not a baseline zero")
    out: dict[str, int] = {}
    for v in range(g.n):
        for field in ("u", "z", "ell", "f", "c", "alpha", "g", "h"):
            out[f"{field}_{v}"] = old[f"{field}_{v}"]
        out[f"k_{v}"] = old[f"e_{v}"]-old[f"c_{v}"]
        out[f"beta_{v}"] = old[f"c_{v}"]*old[f"gamma_{v}"]
    for v, j in edges(g):
        p, pp = old[f"p_{v}_{j}"], old[f"p_{j}_{v}"]
        q, qq = old[f"q_{v}_{j}"], old[f"q_{j}_{v}"]
        lo, neg, eq, pos, hi = 1-q, q-p, p+pp-1, qq-pp, 1-qq
        delta = old[f"r_{j}"]-old[f"r_{v}"]
        gap = lo*(-delta-2)+hi*(delta-2)
        vals = lo, neg, eq, pos, hi, gap
        out.update((f"{field}_{v}_{j}", val) for field, val in zip(EDGE_FIELDS, vals))
    if evaluate(g, eta, out) != 0:
        raise AssertionError("zero-set projection failed")
    return out


def to_baseline(g: Graph, eta: Sequence[int], new: Mapping[str, int]) -> dict[str, int]:
    from sandpile_cubic import comparison_data, evaluate as baseline_evaluate
    if evaluate(g, eta, new) != 0:
        raise ValueError("not a compact zero")
    out: dict[str, int] = {}
    r = [new[f"k_{v}"]+2*new[f"c_{v}"]+new[f"beta_{v}"] for v in range(g.n)]
    for v in range(g.n):
        for field in ("u", "z", "ell", "f", "c", "alpha", "g", "h"):
            out[f"{field}_{v}"] = new[f"{field}_{v}"]
        e = new[f"k_{v}"]+new[f"c_{v}"]
        c = new[f"c_{v}"]
        out[f"r_{v}"] = r[v]
        out[f"e_{v}"] = e
        out[f"beta_{v}"] = e*(r[v]-1)
        out[f"cb_{v}"] = 1-c
        out[f"gamma_{v}"] = c*(r[v]-2)+(1-c)*(1-r[v])
    for v, j in g.edges:
        vals = comparison_data(r[j], r[v])+comparison_data(r[j]+1, r[v])
        out.update((f"{field}_{v}_{j}", val) for field, val in zip(
            ("p", "pb", "s", "q", "qb", "t"), vals))
    if baseline_evaluate(g, eta, out) != 0:
        raise AssertionError("zero-set lifting failed")
    return out


def symbolic_polynomial(g: Graph) -> tuple[Any, tuple[Any, ...], tuple[Any, ...]]:
    import sympy as sp
    eta = tuple(sp.Symbol(f"eta_{v}") for v in range(g.n))
    ws = tuple(sp.Symbol(name) for name in names(g))
    expression = sp.expand(sum(polynomial_terms(g, eta, dict(zip(names(g), ws)))))
    return sp.Poly(expression, *(eta+ws), domain=sp.ZZ), eta, ws


if __name__ == "__main__":
    graph = Graph(((0, 1), (1, 0)), (2, 2))
    t = 10**100+7
    w = certificate(graph, (t, 0), ((2*t-1)//3, (t-1)//3))
    print("compact coordinates:", len(w))
    print("compact summands:", len(polynomial_terms(graph, (t, 0), w)))
    print("exact value:", evaluate(graph, (t, 0), w))
