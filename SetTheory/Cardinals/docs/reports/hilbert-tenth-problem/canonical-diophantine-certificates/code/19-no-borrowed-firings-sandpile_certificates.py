#!/usr/bin/env python3
"""Exact, history-free natural-number certificates for undirected sandpiles.

Python >= 3.10; standard library only. See article.tex for the mathematical
proof. Tests are finite checks, not substitutes for that proof.

Polynomials are expanded sparse integer polynomials, not symbolic predicates.
The compiler returns all quadratic residuals; Certificate.quartic() expands
one genuine quartic polynomial. Expand only for modest graphs.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable, Mapping, Sequence
import json


def natural(x: object) -> bool:
    return type(x) is int and x >= 0


class Poly:
    """Sparse polynomial: monomials are sorted tuples of variable indices."""
    __slots__ = ("terms",)

    def __init__(self, terms: Mapping[tuple[int, ...], int] | None = None):
        canonical: dict[tuple[int, ...], int] = {}
        for monomial, coefficient in (terms or {}).items():
            if type(coefficient) is not int or not all(natural(i) for i in monomial):
                raise TypeError("Integer coefficients and natural variable indices are required")
            key = tuple(sorted(monomial))
            canonical[key] = canonical.get(key, 0) + coefficient
        self.terms = {key: value for key, value in canonical.items() if value}

    @staticmethod
    def const(k: int) -> Poly:
        if type(k) is not int:
            raise TypeError("Polynomial coefficients must be integers")
        return Poly({(): k})

    @staticmethod
    def var(i: int) -> Poly:
        return Poly({(i,): 1})

    @staticmethod
    def coerce(x: int | Poly) -> Poly:
        return x if isinstance(x, Poly) else Poly.const(x)

    def __add__(self, other: int | Poly) -> Poly:
        ans = dict(self.terms)
        for k, v in self.coerce(other).terms.items():
            ans[k] = ans.get(k, 0) + v
        return Poly(ans)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other: int | Poly) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: int | Poly) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: int | Poly) -> Poly:
        ans: dict[tuple[int, ...], int] = {}
        for k, v in self.terms.items():
            for l, w in self.coerce(other).terms.items():
                mon = tuple(sorted(k + l))
                ans[mon] = ans.get(mon, 0) + v * w
        return Poly(ans)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Sequence[int]) -> int:
        result = 0
        for mon, coefficient in self.terms.items():
            term = coefficient
            for index in mon:
                term *= values[index]
            result += term
        return result

    def serialize(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items(), key=lambda kv: (len(kv[0]), kv[0]))]


@dataclass(frozen=True)
class Graph:
    """Loopless undirected multigraph; sinks are encoded by edge counts."""
    adjacency: tuple[tuple[int, ...], ...]
    sink: tuple[int, ...]

    def __post_init__(self) -> None:
        # Copy mutable caller inputs before validation and retention.
        object.__setattr__(self, "adjacency", tuple(tuple(row) for row in self.adjacency))
        object.__setattr__(self, "sink", tuple(self.sink))
        n = len(self.sink)
        if n == 0 or len(self.adjacency) != n:
            raise ValueError("A nonempty square graph is required")
        if any(len(row) != n for row in self.adjacency):
            raise ValueError("Adjacency must be square")
        if not all(natural(x) for row in self.adjacency for x in row):
            raise ValueError("Adjacency entries must be nonnegative integers")
        if not all(natural(x) for x in self.sink):
            raise ValueError("Sink multiplicities must be nonnegative integers")
        for i in range(n):
            if self.adjacency[i][i] != 0:
                raise ValueError("Self-loops are not supported")
            for j in range(n):
                if self.adjacency[i][j] != self.adjacency[j][i]:
                    raise ValueError("The burning compiler requires symmetry")
        if any(x == 0 for x in self.degree):
            raise ValueError("Every nonsink vertex needs positive degree")

    @property
    def n(self) -> int:
        return len(self.sink)

    @property
    def degree(self) -> tuple[int, ...]:
        return tuple(sum(row) + b for row, b in zip(self.adjacency, self.sink))

    @property
    def m(self) -> int:
        return sum(self.adjacency[i][j] > 0 for i in range(self.n)
                   for j in range(i + 1, self.n))

    def neighbors(self, i: int) -> Iterable[tuple[int, int]]:
        return ((j, a) for j, a in enumerate(self.adjacency[i]) if a)

    def all_components_dissipative(self) -> bool:
        reached = {i for i, b in enumerate(self.sink) if b}
        stack = list(reached)
        while stack:
            i = stack.pop()
            for j, _ in self.neighbors(i):
                if j not in reached:
                    reached.add(j)
                    stack.append(j)
        return len(reached) == self.n


def validate_vector(graph: Graph, values: Sequence[int], label: str) -> None:
    if len(values) != graph.n or not all(natural(x) for x in values):
        raise ValueError(f"{label} must be a natural vector of length {graph.n}")


def final_state(graph: Graph, chips: Sequence[int], u: Sequence[int]) -> tuple[int, ...]:
    validate_vector(graph, chips, "chips")
    validate_vector(graph, u, "odometer")
    return tuple(chips[i] - graph.degree[i] * u[i]
                 + sum(a * u[j] for j, a in graph.neighbors(i))
                 for i in range(graph.n))


def stabilize(graph: Graph, chips: Sequence[int], *, max_batches: int = 1_000_000
              ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Greedy legal batched firing. Budget exhaustion means UNKNOWN, not divergence."""
    validate_vector(graph, chips, "chips")
    if not natural(max_batches):
        raise ValueError("max_batches must be a nonnegative integer")
    c, u = list(chips), [0] * graph.n
    d = graph.degree
    batches = 0
    while True:
        i = next((v for v in range(graph.n) if c[v] >= d[v]), None)
        if i is None:
            return tuple(u), tuple(c)
        if batches >= max_batches:
            raise TimeoutError("Firing budget exhausted; termination status is unknown")
        q = c[i] // d[i]
        c[i] -= q * d[i]
        u[i] += q
        for j, a in graph.neighbors(i):
            c[j] += q * a
        batches += 1


def burning_ranks(graph: Graph, u: Sequence[int], s: Sequence[int]) -> tuple[int, ...]:
    validate_vector(graph, u, "odometer")
    validate_vector(graph, s, "stable configuration")
    if any(s[i] >= graph.degree[i] for i in range(graph.n)):
        raise ValueError("Final state is not stable")
    active = {i for i in range(graph.n) if u[i]}
    ranks = [0] * graph.n
    round_number = 1
    while active:
        burned = {i for i in active
                  if s[i] >= sum(graph.adjacency[i][j] for j in active)}
        if not burned:
            raise ValueError("Fired support contains a forbidden subconfiguration")
        for i in burned:
            ranks[i] = round_number
        active -= burned
        round_number += 1
    return tuple(ranks)


def rank_conditions(graph: Graph, u: Sequence[int], s: Sequence[int],
                    r: Sequence[int]) -> bool:
    """Direct semantic checker, deliberately independent of polynomial compilation."""
    if any(len(v) != graph.n for v in (u, s, r)):
        return False
    if not all(natural(x) for v in (u, s, r) for x in v):
        return False
    for i in range(graph.n):
        if s[i] >= graph.degree[i] or ((u[i] > 0) != (r[i] > 0)):
            return False
        if r[i] > 0:
            k = sum(a for j, a in graph.neighbors(i) if r[j] >= r[i])
            if s[i] < k:
                return False
        if r[i] > 1:
            h = sum(a for j, a in graph.neighbors(i) if r[j] >= r[i] - 1)
            if s[i] >= h:
                return False
    return True


VERTEX_FIELDS = ("u", "s", "sigma", "z", "alpha", "r", "k", "e", "beta", "lam", "mu")


class Certificate:
    def __init__(self) -> None:
        self.variables: list[str] = []
        self.index: dict[str, int] = {}
        self.residuals: list[Poly] = []
        self.labels: list[str] = []

    def var(self, name: str) -> Poly:
        if name in self.index:
            raise ValueError(f"Duplicate variable: {name}")
        index = len(self.variables)
        self.index[name] = index
        self.variables.append(name)
        return Poly.var(index)

    def add(self, label: str, residual: Poly) -> None:
        if residual.degree > 2:
            raise ValueError("Residual is not quadratic")
        self.labels.append(label)
        self.residuals.append(residual)

    def nz(self, label: str, x: Poly, z: Poly, a: Poly) -> None:
        self.add(label + ".boolean", z * (z - 1))
        self.add(label + ".value", x - z * (a + 1))
        self.add(label + ".inactive", (1 - z) * a)

    def ge(self, label: str, x: Poly, y: Poly) -> tuple[Poly, Poly, Poly]:
        b, p, q = (self.var(label + "." + name) for name in ("b", "p", "q"))
        self.add(label + ".boolean", b * (b - 1))
        self.add(label + ".difference", x - y - b * p + (1 - b) * (q + 1))
        self.add(label + ".inactive_p", (1 - b) * p)
        self.add(label + ".inactive_q", b * q)
        return b, p, q

    def vector(self, assignment: Mapping[str, int]) -> tuple[int, ...]:
        if set(assignment) != set(self.variables):
            missing = set(self.variables) - set(assignment)
            extra = set(assignment) - set(self.variables)
            raise ValueError(f"Assignment mismatch; missing={missing}, extra={extra}")
        result = tuple(assignment[n] for n in self.variables)
        if not all(natural(v) for v in result):
            raise ValueError("Every witness must be a nonnegative integer")
        return result

    def evaluate(self, values: Sequence[int]) -> tuple[int, ...]:
        if len(values) != len(self.variables) or not all(natural(x) for x in values):
            raise ValueError("Invalid natural witness tuple")
        return tuple(p.evaluate(values) for p in self.residuals)

    def quartic(self) -> Poly:
        return sum((f * f for f in self.residuals), Poly.const(0))

    def serialize(self, *, expand_quartic: bool = False) -> dict:
        data = {"domain": "nonnegative integers", "variables": self.variables,
                "residuals": [{"label": label, "terms": f.serialize()}
                              for label, f in zip(self.labels, self.residuals)],
                "variable_count": len(self.variables), "residual_count": len(self.residuals)}
        if expand_quartic:
            q = self.quartic()
            data.update(quartic=q.serialize(), degree=q.degree, monomial_count=len(q.terms))
        return data


def compile_graph(graph: Graph, chips: Sequence[int]) -> Certificate:
    validate_vector(graph, chips, "chips")
    cert = Certificate()
    ports = [{name: cert.var(f"v{i}.{name}") for name in VERTEX_FIELDS}
             for i in range(graph.n)]
    for i, v in enumerate(ports):
        ksum, hsum = Poly.const(0), Poly.const(0)
        for j, a in graph.neighbors(i):
            aa, _, _ = cert.ge(f"a{i}_{j}", ports[j]["r"], v["r"])
            bb, _, _ = cert.ge(f"b{i}_{j}", ports[j]["r"], v["r"] - 1)
            ksum += a * aa
            hsum += a * bb
        label = f"v{i}"
        cert.add(label + ".balance", v["s"] - chips[i] + graph.degree[i] * v["u"]
                 - sum((a * ports[j]["u"] for j, a in graph.neighbors(i)), Poly.const(0)))
        cert.add(label + ".stable", v["s"] + v["sigma"] - (graph.degree[i] - 1))
        cert.nz(label + ".active", v["u"], v["z"], v["alpha"])
        cert.add(label + ".rank", v["r"] - v["z"] - v["k"])
        cert.add(label + ".rank_inactive", (1 - v["z"]) * v["k"])
        cert.nz(label + ".later", v["k"], v["e"], v["beta"])
        cert.add(label + ".burn_now", v["lam"] - v["z"] * (v["s"] - ksum))
        cert.add(label + ".not_before", v["mu"] - v["e"] * (hsum - v["s"] - 1))
    assert len(cert.variables) == 11 * graph.n + 12 * graph.m
    assert len(cert.residuals) == 12 * graph.n + 16 * graph.m
    return cert


def ge_values(x: int, y: int) -> tuple[int, int, int]:
    return (1, x - y, 0) if x >= y else (0, 0, y - x - 1)


def graph_assignment(graph: Graph, chips: Sequence[int], u: Sequence[int] | None = None
                     ) -> dict[str, int]:
    if u is None:
        u, s = stabilize(graph, chips)
    else:
        s = final_state(graph, chips, u)
    r = burning_ranks(graph, u, s)
    answer: dict[str, int] = {}
    for i in range(graph.n):
        z = int(u[i] > 0)
        k = r[i] - z
        e = int(k > 0)
        ks = sum(a for j, a in graph.neighbors(i) if r[j] >= r[i])
        hs = sum(a for j, a in graph.neighbors(i) if r[j] >= r[i] - 1)
        values = (u[i], s[i], graph.degree[i] - 1 - s[i], z, max(u[i] - 1, 0),
                  r[i], k, e, max(k - 1, 0), z * (s[i] - ks), e * (hs - s[i] - 1))
        for name, value in zip(VERTEX_FIELDS, values):
            answer[f"v{i}.{name}"] = value
        for j, _ in graph.neighbors(i):
            for prefix, threshold in (("a", r[i]), ("b", r[i] - 1)):
                for name, value in zip(("b", "p", "q"), ge_values(r[j], threshold)):
                    answer[f"{prefix}{i}_{j}.{name}"] = value
    return answer


def cube_graph(dimension: int, radius: int) -> tuple[Graph, tuple[tuple[int, ...], ...]]:
    if type(dimension) is not int or dimension < 1 or not natural(radius):
        raise ValueError("dimension >= 1 and radius >= 0 are required")
    points = tuple(product(range(-radius, radius + 1), repeat=dimension))
    lookup = {x: i for i, x in enumerate(points)}
    a = [[0] * len(points) for _ in points]
    sink = [0] * len(points)
    for i, x in enumerate(points):
        for y in lattice_neighbors(x):
            if y in lookup:
                a[i][lookup[y]] = 1
            else:
                sink[i] += 1
    return Graph(tuple(map(tuple, a)), tuple(sink)), points


def lattice_neighbors(x: tuple[int, ...]) -> Iterable[tuple[int, ...]]:
    for axis in range(len(x)):
        for sign in (-1, 1):
            y = list(x)
            y[axis] += sign
            yield tuple(y)


def compile_cube(dimension: int, radius: int, eta: Callable[[tuple[int, ...]], int]
                 ) -> tuple[Certificate, Graph, tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]]:
    """Compile a cube with no-firing halo. Caller must ensure eta is stable farther out.

    For periodic-plus-finite inputs, also require every perturbation inside
    the cube. This finite routine does not inspect an arbitrary infinite eta.
    """
    graph, points = cube_graph(dimension, radius)
    lookup = {x: i for i, x in enumerate(points)}
    chips = tuple(eta(x) for x in points)
    cert = compile_graph(graph, chips)
    halo = tuple(sorted({y for x in points for y in lattice_neighbors(x) if y not in lookup}))
    for index, y in enumerate(halo):
        value = eta(y)
        if not natural(value):
            raise ValueError("eta must be natural-valued on the cube and halo")
        slack = cert.var(f"halo{index}.slack")
        flux = sum((Poly.var(cert.index[f"v{lookup[x]}.u"])
                    for x in lattice_neighbors(y) if x in lookup), Poly.const(0))
        cert.add(f"halo{index}.stable", slack + value + flux - (2 * dimension - 1))
    return cert, graph, points, halo


def cube_assignment(graph: Graph, points: Sequence[tuple[int, ...]],
                    halo: Sequence[tuple[int, ...]], eta: Callable[[tuple[int, ...]], int]
                    ) -> dict[str, int]:
    chips = tuple(eta(x) for x in points)
    answer = graph_assignment(graph, chips)
    lookup = {x: i for i, x in enumerate(points)}
    threshold = 2 * len(points[0])
    for index, y in enumerate(halo):
        flux = sum(answer[f"v{lookup[x]}.u"] for x in lattice_neighbors(y) if x in lookup)
        slack = threshold - 1 - eta(y) - flux
        if slack < 0:
            raise ValueError("Halo becomes unstable: the cube does not contain stabilization")
        answer[f"halo{index}.slack"] = slack
    return answer



@dataclass(frozen=True)
class PeriodicInput:
    """An effective stable periodic background plus finitely many added chips.

    The background table is flattened in lexicographic product order for
    range(periods[0]) x ... x range(periods[d-1]). Additions use distinct
    integer lattice sites and strictly positive amounts; both are copied.
    """
    periods: tuple[int, ...]
    background: tuple[int, ...]
    additions: tuple[tuple[tuple[int, ...], int], ...] = ()

    def __post_init__(self) -> None:
        from math import prod
        object.__setattr__(self, "periods", tuple(self.periods))
        object.__setattr__(self, "background", tuple(self.background))
        object.__setattr__(self, "additions", tuple((tuple(x), a) for x, a in self.additions))
        if not self.periods or not all(natural(p) and p > 0 for p in self.periods):
            raise ValueError("Periods must be positive integers in positive dimension")
        if len(self.background) != prod(self.periods):
            raise ValueError("The full periodic table must be supplied")
        if not all(natural(b) and b < 2 * self.dimension for b in self.background):
            raise ValueError("The periodic background must be nonnegative and stable")
        sites = set()
        for x, a in self.additions:
            if len(x) != self.dimension or not all(type(t) is int for t in x):
                raise ValueError("An addition site must have integer coordinates of the correct dimension")
            if not natural(a) or a == 0 or x in sites:
                raise ValueError("Additions must have distinct sites and positive integer amounts")
            sites.add(x)
        object.__setattr__(self, "additions", tuple(sorted(self.additions)))

    @property
    def dimension(self) -> int:
        return len(self.periods)

    @property
    def perturbation_radius(self) -> int:
        return max((abs(t) for x, _ in self.additions for t in x), default=0)

    def background_value(self, x: tuple[int, ...]) -> int:
        if len(x) != self.dimension or not all(type(t) is int for t in x):
            raise ValueError("Invalid lattice coordinate")
        index = 0
        for t, period in zip(x, self.periods):
            index = index * period + t % period
        return self.background[index]

    def value(self, x: tuple[int, ...]) -> int:
        return self.background_value(x) + sum(a for y, a in self.additions if x == y)


def compile_periodic_cube(data: PeriodicInput, radius: int):
    """Sound finite-window interface: validates the stable tail and input support."""
    if not natural(radius) or radius < data.perturbation_radius:
        raise ValueError("The cube must contain every input perturbation")
    return compile_cube(data.dimension, radius, data.value)



def field_names(dimension: int) -> tuple[str, ...]:
    return VERTEX_FIELDS + tuple(f"dir{j}.{name}" for j in range(2 * dimension)
                                 for name in ("A", "p", "q", "B", "P", "Q"))


def field_tail(data: PeriodicInput, x: tuple[int, ...]) -> tuple[int, ...]:
    b = data.background_value(x)
    return (0, b, 2 * data.dimension - 1 - b, 0, 0, 0, 0, 0, 0, 0, 0) + (
        1, 0, 0, 1, 1, 0) * (2 * data.dimension)


def field_witness_from_cube(data: PeriodicInput, radius: int
                            ) -> dict[tuple[int, ...], tuple[int, ...]]:
    """Return a normalized finite exception table, with no box in the witness.

    Raises ValueError when the window leaks; a failed small window says
    nothing by itself about whether global finite stabilization occurs.
    """
    if not natural(radius) or radius < data.perturbation_radius:
        raise ValueError("The cube must contain the input perturbations")
    graph, points = cube_graph(data.dimension, radius)
    chips = tuple(data.value(x) for x in points)
    u, s = stabilize(graph, chips)
    r = burning_ranks(graph, u, s)
    up = {x: u[i] for i, x in enumerate(points) if u[i]}
    rp = {x: r[i] for i, x in enumerate(points) if r[i]}
    region = set(up) | {x for x, _ in data.additions}
    region |= {y for x in up for y in lattice_neighbors(x)}
    result = {}
    for x in sorted(region):
        ux, rx = up.get(x, 0), rp.get(x, 0)
        sx = data.value(x) - 2 * data.dimension * ux + sum(up.get(y, 0) for y in lattice_neighbors(x))
        z = int(ux > 0)
        k = rx - z
        e = int(k > 0)
        comparisons = []
        for y in lattice_neighbors(x):
            comparisons.extend(ge_values(rp.get(y, 0), rx))
            comparisons.extend(ge_values(rp.get(y, 0), rx - 1))
        ks = sum(comparisons[6 * j] for j in range(2 * data.dimension))
        hs = sum(comparisons[6 * j + 3] for j in range(2 * data.dimension))
        values = (ux, sx, 2 * data.dimension - 1 - sx, z, max(ux - 1, 0), rx, k,
                  e, max(k - 1, 0), z * (sx - ks), e * (hs - sx - 1)) + tuple(comparisons)
        if not all(natural(v) for v in values):
            raise ValueError("The supplied cube does not contain global stabilization")
        if values != field_tail(data, x):
            result[x] = values
    if not verify_field_witness(data, result):
        raise AssertionError("Internal error while generating a field witness")
    return result


def field_residuals_at(data: PeriodicInput,
                       exceptions: Mapping[tuple[int, ...], Sequence[int]],
                       x: tuple[int, ...]) -> tuple[int, ...]:
    """The literal local 12+16d residual values. Does not simulate any firing."""
    def get(y):
        return exceptions.get(y, field_tail(data, y))
    values = get(x)
    u, s, sigma, z, alpha, r, k, e, beta, lam, mu = values[:11]
    neighbors = tuple(lattice_neighbors(x))
    neighbor_values = [get(y) for y in neighbors]
    ks = hs = 0
    comparisons = []
    for j, neighbor in enumerate(neighbor_values):
        A, p, q, B, P, Q = values[11 + 6*j:17 + 6*j]
        ks += A
        hs += B
        nr = neighbor[5]
        comparisons += [A*(A-1), nr-r-A*p+(1-A)*(q+1), (1-A)*p, A*q,
                        B*(B-1), nr-r+1-B*P+(1-B)*(Q+1), (1-B)*P, B*Q]
    residuals = [s-data.value(x)+2*data.dimension*u-sum(nv[0] for nv in neighbor_values),
                 s+sigma-(2*data.dimension-1), z*(z-1), u-z*(alpha+1), (1-z)*alpha,
                 r-z-k, (1-z)*k, e*(e-1), k-e*(beta+1), (1-e)*beta,
                 lam-z*(s-ks), mu-e*(hs-s-1)] + comparisons
    return tuple(residuals)


def verify_field_witness(data: PeriodicInput,
                         exceptions: Mapping[tuple[int, ...], Sequence[int]]) -> bool:
    """Independent local verifier for canonical finite-deviation field tables.

    A Python mapping already has distinct keys. A serialized list loader
    must reject duplicate coordinates before constructing this mapping.
    The function rejects redundant tail entries, enforcing normalization.
    """
    arity = 11 + 12 * data.dimension
    for x, values in exceptions.items():
        if len(x) != data.dimension or not all(type(t) is int for t in x):
            return False
        if len(values) != arity or not all(natural(v) for v in values):
            return False
        if tuple(values) == field_tail(data, x):
            return False
    region = set(exceptions)
    region |= {y for x in exceptions for y in lattice_neighbors(x)}
    region |= {x for x, _ in data.additions}
    return all(not any(field_residuals_at(data, exceptions, x)) for x in region)


def serialize_field_witness(data: PeriodicInput,
                            exceptions: Mapping[tuple[int, ...], Sequence[int]]) -> dict:
    if not verify_field_witness(data, exceptions):
        raise ValueError("Invalid field witness")
    return {"format": "sandpile-field-certificate-v1", "periods": list(data.periods),
            "background": list(data.background),
            "additions": [{"site": list(x), "chips": a} for x, a in data.additions],
            "field_names": list(field_names(data.dimension)),
            "exceptions": [{"site": list(x), "values": list(exceptions[x])}
                           for x in sorted(exceptions)]}


def read_field_witness(document: Mapping) -> tuple[PeriodicInput, dict]:
    """Load and verify the normalized JSON representation; reject duplicates."""
    try:
        if document["format"] != "sandpile-field-certificate-v1":
            raise ValueError("Unknown field-certificate format")
        data = PeriodicInput(tuple(document["periods"]), tuple(document["background"]),
                             tuple((tuple(row["site"]), row["chips"]) for row in document["additions"]))
        if tuple(document["field_names"]) != field_names(data.dimension):
            raise ValueError("Incorrect field names or ordering")
        exceptions = {}
        previous = None
        for row in document["exceptions"]:
            x = tuple(row["site"])
            if previous is not None and x <= previous:
                raise ValueError("Exception sites must be distinct and sorted")
            previous = x
            exceptions[x] = tuple(row["values"])
        if not verify_field_witness(data, exceptions):
            raise ValueError("The local field equations do not hold")
        return data, exceptions
    except (KeyError, TypeError, IndexError) as exc:
        raise ValueError("Malformed field-certificate document") from exc


if __name__ == "__main__":
    graph = Graph(((0, 1), (1, 0)), (1, 1))
    cert = compile_graph(graph, (3, 1))
    assignment = graph_assignment(graph, (3, 1))
    assert not any(cert.evaluate(cert.vector(assignment)))
    print(json.dumps({"variables": len(cert.variables), "residuals": len(cert.residuals),
                      "degree": cert.quartic().degree, "odometer": [2, 1],
                      "parallel_burning_ranks": [2, 1]}, indent=2))
