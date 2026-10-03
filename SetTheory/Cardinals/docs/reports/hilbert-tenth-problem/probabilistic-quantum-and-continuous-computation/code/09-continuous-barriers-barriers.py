"""Exact rational algorithms accompanying Diophantine Barriers.

Python 3.10+, standard library only.  These are reference implementations,
not a polynomial-time algorithm or a formal proof.  The global PWA compiler
accepts a binary Turing-machine transition table; no universal table is
bundled.  Noise is measured only between complete discrete-time map steps.
"""
from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Callable, Iterable, Mapping, Sequence

Point = tuple[F, ...]
Map = Callable[[Point], Point]


def norm_inf(x: Sequence[F], y: Sequence[F]) -> F:
    if len(x) != len(y) or not x:
        raise ValueError("Points must have the same positive dimension")
    return max(abs(a-b) for a, b in zip(x, y))


@dataclass(frozen=True)
class Box:
    lower: Point
    upper: Point

    def __post_init__(self) -> None:
        if not self.lower or len(self.lower) != len(self.upper):
            raise ValueError("Invalid box dimension")
        if any(a < 0 or b > 1 or a > b for a, b in zip(self.lower, self.upper)):
            raise ValueError("Box must be a nonempty closed subbox of the cube")

    def contains(self, x: Point) -> bool:
        return len(x) == len(self.lower) and all(
            a <= t <= b for a, t, b in zip(self.lower, x, self.upper))


@dataclass
class GridGraph:
    vertices: tuple[Point, ...]
    source: int
    targets: frozenset[int]
    weights: tuple[tuple[F, ...], ...]
    mesh: int
    lipschitz: F

    @property
    def error(self) -> F:
        return (self.lipschitz + 1) / (2 * self.mesh)

    @property
    def threshold(self) -> F:
        return (self.lipschitz + 1) / self.mesh


def make_grid_graph(f: Map, x: Point, boxes: Sequence[Box], mesh: int,
                    lipschitz: F, *, max_vertices: int = 2000) -> GridGraph:
    """Build the complete weighted graph. L is an externally certified bound.

    Runtime/memory scale quadratically in the vertex count.  This function
    checks geometry but cannot verify the supplied global Lipschitz bound.
    """
    d = len(x)
    if d == 0 or mesh < 1 or lipschitz < 0:
        raise ValueError("Invalid dimension, mesh, or Lipschitz bound")
    if any(t < 0 or t > 1 for t in x) or not boxes:
        raise ValueError("Invalid initial point or empty target")
    if any(len(b.lower) != d for b in boxes):
        raise ValueError("Target dimension mismatch")
    if any(b.contains(x) for b in boxes):
        raise ValueError("Initial point already in target: radius is defined as zero")
    endpoints = [t for b in boxes for t in b.lower + b.upper]
    if any((mesh*t).denominator != 1 for t in endpoints):
        raise ValueError("Target endpoints must be aligned with the grid")
    if (mesh+1)**d + 1 > max_vertices:
        raise ValueError("Grid exceeds explicit reference-implementation size limit")
    grid = tuple(product(*(tuple(F(j, mesh) for j in range(mesh+1)) for _ in x)))
    vertices = grid if x in grid else grid + (x,)
    source = vertices.index(x)
    targets = frozenset(i for i, p in enumerate(vertices)
                        if any(b.contains(p) for b in boxes))
    images = tuple(f(p) for p in vertices)
    if any(len(y) != d or any(t < 0 or t > 1 for t in y) for y in images):
        raise ValueError("Map returned a point outside the cube")
    weights = tuple(tuple(norm_inf(y, v) for v in vertices) for y in images)
    return GridGraph(vertices, source, targets, weights, mesh, lipschitz)


def bottleneck(weights: Sequence[Sequence[F]], source: int,
               targets: Iterable[int]) -> F:
    """Minimize the maximum edge weight along a directed source-target path."""
    n = len(weights)
    if not 0 <= source < n or any(len(row) != n for row in weights):
        raise ValueError("Invalid square matrix or source")
    target_set = set(targets)
    if not target_set or not target_set <= set(range(n)):
        raise ValueError("Invalid targets")
    if any(w < 0 for row in weights for w in row):
        raise ValueError("Weights must be nonnegative")
    dist: list[F | None] = [None] * n
    dist[source] = F(0)
    done: set[int] = set()
    for _ in range(n):
        u = min((i for i in range(n) if i not in done and dist[i] is not None),
                key=lambda i: dist[i])
        current = dist[u]
        assert current is not None
        if u in target_set:
            return current
        done.add(u)
        for v in range(n):
            candidate = max(current, weights[u][v])
            if v not in done and (dist[v] is None or candidate < dist[v]):
                dist[v] = candidate
    raise AssertionError("A complete graph always has a target path")


def reachable_below(weights: Sequence[Sequence[F]], source: int,
                    threshold: F) -> frozenset[int]:
    """Reachability using edges with weight STRICTLY below threshold."""
    seen = {source}
    stack = [source]
    while stack:
        u = stack.pop()
        for v, weight in enumerate(weights[u]):
            if v not in seen and weight < threshold:
                seen.add(v)
                stack.append(v)
    return frozenset(seen)


def quartic_value(graph: GridGraph, bits: Sequence[int]) -> int:
    """Evaluate the explicit sum-of-squares Q_N at an integer assignment."""
    n = len(graph.vertices)
    if len(bits) != n or any(not isinstance(b, int) for b in bits):
        raise ValueError("Expected one integer per vertex")
    value = (bits[graph.source]-1)**2
    value += sum(bits[t]**2 for t in graph.targets)
    value += sum((b*(b-1))**2 for b in bits)
    value += sum((bits[u]*(1-bits[v]))**2 for u in range(n) for v in range(n)
                 if graph.weights[u][v] < graph.threshold)
    return value


def safety_certificate(graph: GridGraph) -> tuple[int, ...] | None:
    """Return Boolean Q_N=0 witnesses, or None when this mesh does not certify."""
    inside = reachable_below(graph.weights, graph.source, graph.threshold)
    if inside & graph.targets:
        return None
    bits = tuple(int(i in inside) for i in range(len(graph.vertices)))
    assert quartic_value(graph, bits) == 0
    return bits


def quartic_expression(graph: GridGraph) -> str:
    """Human-readable exact polynomial in factored sum-of-squares form."""
    terms = [f"(b{graph.source}-1)^2"]
    terms += [f"b{t}^2" for t in sorted(graph.targets)]
    terms += [f"(b{i}*(b{i}-1))^2" for i in range(len(graph.vertices))]
    terms += [f"(b{u}*(1-b{v}))^2" for u in range(len(graph.vertices))
              for v in range(len(graph.vertices))
              if graph.weights[u][v] < graph.threshold]
    return " +\n".join(terms) + "\n"


@dataclass(frozen=True)
class Transition:
    next_state: int
    write: int
    move: str


def tape_update(u: F, v: F, left_bit: int, read: int, write: int,
                move: str) -> tuple[F, F]:
    """Affine update on the full closed digit rectangle, not only Cantor points."""
    if (left_bit not in (0, 1) or read not in (0, 1) or write not in (0, 1)
            or move not in ("L", "R", "S")):
        raise ValueError("Invalid binary Turing-machine operation")
    if move == "R":
        return (2*write+u)/3, 3*v-2*read
    if move == "L":
        return 3*u-2*left_bit, v/3 + F(2*left_bit, 3) + F(2*(write-read), 9)
    return u, v + F(2*(write-read), 3)


@dataclass
class BinaryMachine:
    states: int
    start: int
    accept: int
    reject: int
    transitions: Mapping[tuple[int, int], Transition]

    def __post_init__(self) -> None:
        if self.states < 3 or len({self.start, self.accept, self.reject}) != 3:
            raise ValueError("Need distinct start/accept/reject states")
        if any(not 0 <= j < self.states for j in (self.start, self.accept, self.reject)):
            raise ValueError("Invalid distinguished state")
        for j in range(self.states):
            if j in (self.accept, self.reject):
                continue
            for a in (0, 1):
                tr = self.transitions.get((j, a))
                if tr is None or not 0 <= tr.next_state < self.states:
                    raise ValueError("Transition table is incomplete")
                if tr.write not in (0, 1) or tr.move not in ("L", "R", "S"):
                    raise ValueError("Malformed transition")


class PackedPWA:
    """Three-dimensional rational continuous PWA extension of a binary TM.

    Coordinate order: packed state/left tape xi, right tape v, emergency z.
    Uses a globally consistent Kuhn triangulation of a rectilinear grid.
    The transition table is a parameter of this compiler, not an input of
    the compiled map.  The universality theorem fixes a universal table.
    """
    def __init__(self, machine: BinaryMachine):
        self.machine = machine
        self.beta = F(1, 3*machine.states)
        self.alpha = tuple((3*j+1)*self.beta for j in range(machine.states))
        self.lipschitz = F(9*machine.states + 6)
        axis = {F(0), F(1)}
        for a in self.alpha:
            axis.update(a + self.beta*F(k, 3) for k in range(4))
        for j in (machine.accept, machine.reject):
            axis.update((self.alpha[j]-self.beta/2, self.alpha[j]+3*self.beta/2))
        ternary = (F(0), F(1, 3), F(2, 3), F(1))
        self.axes = (tuple(sorted(axis)), ternary, ternary)
        self._vertex_cache: dict[Point, Point] = {}

    def sink(self, j: int) -> Point:
        return self.alpha[j]+self.beta/2, F(1, 2), F(1, 2)

    def initial(self, word: Sequence[int]) -> Point:
        if any(a not in (0, 1) for a in word):
            raise ValueError("Input must be binary")
        v = sum((F(2*a, 3**(k+1)) for k, a in enumerate(word)), F(0))
        return self.alpha[self.machine.start], v, F(0)

    def target(self, p: Point) -> bool:
        a = self.alpha[self.machine.accept]
        return a <= p[0] <= a + self.beta

    @staticmethod
    def _digit(t: F) -> int | None:
        if 0 <= t <= F(1, 3):
            return 0
        if F(2, 3) <= t <= 1:
            return 1
        return None

    def prescribed(self, p: Point) -> Point | None:
        xi, v, z = p
        for j in (self.machine.accept, self.machine.reject):
            a = self.alpha[j]
            if a-self.beta/2 <= xi <= a+3*self.beta/2:
                return self.sink(j)
        for j, alpha in enumerate(self.alpha):
            if j in (self.machine.accept, self.machine.reject):
                continue
            if alpha <= xi <= alpha+self.beta:
                if F(2, 3) <= z <= 1:
                    return self.sink(self.machine.accept)
                if 0 <= z <= F(1, 3):
                    u = (xi-alpha)/self.beta
                    c, a = self._digit(u), self._digit(v)
                    if c is not None and a is not None:
                        tr = self.machine.transitions[j, a]
                        unew, vnew = tape_update(u, v, c, a, tr.write, tr.move)
                        return self.alpha[tr.next_state]+self.beta*unew, vnew, 3*z
        return None

    def vertex(self, p: Point) -> Point:
        if p not in self._vertex_cache:
            result = self.prescribed(p)
            self._vertex_cache[p] = self.sink(self.machine.reject) if result is None else result
        return self._vertex_cache[p]

    def __call__(self, p: Point) -> Point:
        if len(p) != 3 or any(t < 0 or t > 1 for t in p):
            raise ValueError("Expected a point in the unit cube")
        lo, hi, t = [], [], []
        for a, x in zip(self.axes, p):
            i = min(max(bisect_right(a, x)-1, 0), len(a)-2)
            lo.append(a[i]); hi.append(a[i+1])
            t.append((x-a[i])/(a[i+1]-a[i]))
        order = sorted(range(3), key=lambda i: (-t[i], i))
        vertices = [tuple(lo)]
        current = list(lo)
        for i in order:
            current = current.copy()
            current[i] = hi[i]
            vertices.append(tuple(current))
        lambdas = [1-t[order[0]], t[order[0]]-t[order[1]],
                   t[order[1]]-t[order[2]], t[order[2]]]
        values = [self.vertex(v) for v in vertices]
        return tuple(sum((lam * v[j] for lam, v in zip(lambdas, values)), F(0))
                     for j in range(3))
