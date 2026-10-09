"""Exact weighted orbit profiles for uniform signed-affine fibre systems.

This is a component-query kernel, not an unknot recognizer. All full-fibre
maps are modulo W; sparse defects add specified pointwise identifications.
No production loop enumerates W, a divisor of W, or the lifted components.
"""
from __future__ import annotations
from bisect import bisect_right
from collections import Counter, deque
from dataclasses import dataclass
from hashlib import sha256
from math import gcd
import json
from typing import Any, Callable, Iterable

Vector = tuple[int, ...]
Key = tuple[int, int]
Check = Callable[[], None] | None


def integer(value: Any, name: str = "integer") -> int:
    if type(value) is int:
        return value
    if isinstance(value, str):
        s = value[1:] if value.startswith("-") else value
        if s.startswith("0x") and len(s) > 2:
            try:
                return int(value, 16)
            except ValueError:
                pass
    raise ValueError(f"{name} must be an integer or signed hexadecimal string")


def wire(value: Any) -> Any:
    """Hexadecimal integer transport, with no process-wide digit-limit changes."""
    if type(value) is int:
        return hex(value)
    if isinstance(value, dict):
        return {str(k): wire(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [wire(v) for v in value]
    return value


def digest(value: Any) -> str:
    raw = json.dumps(wire(value), sort_keys=True, separators=(",", ":"))
    return sha256(raw.encode()).hexdigest()


def add(a: Vector, b: Vector) -> Vector:
    return tuple(x + y for x, y in zip(a, b))


def counter_change(c: Counter, key: Vector, amount: int) -> None:
    c[key] += amount
    if c[key] < 0:
        raise ArithmeticError("negative histogram multiplicity")
    if c[key] == 0:
        del c[key]


@dataclass(frozen=True)
class Edge:
    u: int
    v: int
    sign: int
    shift: int


@dataclass(frozen=True)
class Weight:
    v: int
    start: int
    stop: int
    value: Vector


@dataclass(frozen=True)
class Defect:
    u: int
    x: int
    v: int
    y: int
    payload: Vector


@dataclass(frozen=True)
class Model:
    vertices: int
    sheets: int
    dimension: int
    edges: tuple[Edge, ...] = ()
    weights: tuple[Weight, ...] = ()

    @classmethod
    def parse(cls, data: dict[str, Any]) -> Model:
        if not isinstance(data, dict) or set(data) - {
            "vertices", "sheets", "dimension", "edges", "weights"
        }:
            raise ValueError("invalid model fields")
        v = integer(data["vertices"], "vertices")
        w = integer(data["sheets"], "sheets")
        d = integer(data["dimension"], "dimension")
        if min(v, w, d) < 1:
            raise ValueError("vertices, sheets, dimension must be positive")
        edges = []
        for e in data.get("edges", []):
            if not isinstance(e, dict) or set(e) != {"u", "v", "sign", "shift"}:
                raise ValueError("invalid edge fields")
            u, z, s, t = (integer(e[k], k) for k in ("u", "v", "sign", "shift"))
            if not 0 <= u < v or not 0 <= z < v or s not in (-1, 1):
                raise ValueError("invalid edge endpoint or sign")
            edges.append(Edge(u, z, s, t % w))
        weights = []
        for a in data.get("weights", []):
            if not isinstance(a, dict) or set(a) != {"v", "start", "stop", "value"}:
                raise ValueError("invalid weight fields")
            z, l, r = (integer(a[k], k) for k in ("v", "start", "stop"))
            val = tuple(integer(x, "weight coordinate") for x in a["value"])
            if not 0 <= z < v or not 0 <= l < r <= w or len(val) != d:
                raise ValueError("invalid weight interval or dimension")
            weights.append(Weight(z, l, r, val))
        return cls(v, w, d, tuple(edges), tuple(weights))

    def as_dict(self) -> dict[str, Any]:
        return {
            "vertices": self.vertices, "sheets": self.sheets,
            "dimension": self.dimension,
            "edges": [vars(e) for e in self.edges],
            "weights": [vars(w) for w in self.weights],
        }


def parse_defect(data: dict[str, Any], model: Model) -> Defect:
    if not isinstance(data, dict) or set(data) - {"u", "x", "v", "y", "payload"}:
        raise ValueError("invalid defect fields")
    u, x, v, y = (integer(data[k], k) for k in ("u", "x", "v", "y"))
    p = tuple(integer(z, "payload coordinate") for z in data.get(
        "payload", [0] * model.dimension))
    if not (0 <= u < model.vertices and 0 <= v < model.vertices and
            0 <= x < model.sheets and 0 <= y < model.sheets and
            len(p) == model.dimension):
        raise ValueError("invalid defect endpoint or payload dimension")
    return Defect(u, x, v, y, p)


def fixed_residues(d: int, c: int) -> tuple[int, ...]:
    if d % 2:
        return ((c * ((d + 1) // 2)) % d,)
    if c % 2:
        return ()
    return (c // 2, c // 2 + d // 2)


class StepProfile:
    """Residue-class sums of cyclic interval weights on Z/d."""
    def __init__(self, d: int, dimension: int,
                 records: Iterable[tuple[int, int, Vector]], check: Check = None):
        self.d = d
        self.dimension = dimension
        base = [0] * dimension
        events: dict[int, list[int]] = {0: [0] * dimension, d: [0] * dimension}
        self.arcs: list[tuple[int, int, Vector]] = []

        def delta(at: int, val: Vector, factor: int) -> None:
            out = events.setdefault(at, [0] * dimension)
            for j, z in enumerate(val):
                out[j] += factor * z

        for start, length, val in records:
            if check:
                check()
            q, rem = divmod(length, d)
            for j, z in enumerate(val):
                base[j] += q * z
            if not rem:
                continue
            a = start % d
            self.arcs.append((a, rem, val))
            stop = a + rem
            if stop <= d:
                delta(a, val, 1)
                delta(stop, val, -1)
            else:
                delta(a, val, 1)
                delta(d, val, -1)
                delta(0, val, 1)
                delta(stop - d, val, -1)
        self.base = tuple(base)
        self.starts: list[int] = []
        self.stops: list[int] = []
        self.values: list[Vector] = []
        points = sorted(events)
        for a, b in zip(points, points[1:]):
            if check:
                check()
            base = [x + y for x, y in zip(base, events[a])]
            val = tuple(base)
            if self.values and self.values[-1] == val:
                self.stops[-1] = b
            else:
                self.starts.append(a)
                self.stops.append(b)
                self.values.append(val)

    def value(self, residue: int) -> Vector:
        i = bisect_right(self.starts, residue % self.d) - 1
        return self.values[i]

    def histogram(self) -> Counter:
        out: Counter = Counter()
        for a, b, val in zip(self.starts, self.stops, self.values):
            out[val] += b - a
        return out


class Component:
    def __init__(self, root: int, sheets: int, dimension: int,
                 records: list[tuple[int, int, Vector]], d: int,
                 reflection: int | None, check: Check = None):
        self.root, self.sheets, self.dimension = root, sheets, dimension
        self.records = records
        self.d, self.reflection = d, reflection
        self.check = check
        self.rebuilds = 0
        self.rebuild()

    def rebuild(self) -> None:
        self.profile = StepProfile(self.d, self.dimension, self.records, self.check)
        if self.reflection is None:
            self.hist = self.profile.histogram()
            self.count = self.d
            self.folded = None
        else:
            c, d = self.reflection, self.d
            # F(r)+F(c-r): double the constant part, reflect each residual arc.
            records = [(0, d, tuple(2 * x for x in self.profile.base))]
            for a, length, val in self.profile.arcs:
                records.append((a, length, val))
                records.append(((c - a - length + 1) % d, length, val))
            folded = StepProfile(d, self.dimension, records, self.check)
            self.folded = folded
            hist = folded.histogram()
            fixed = fixed_residues(d, c)
            for r in fixed:
                counter_change(hist, folded.value(r), -1)
            if any(n % 2 for n in hist.values()):
                raise ArithmeticError("reflection-pair multiplicity is not even")
            hist = Counter({val: n // 2 for val, n in hist.items() if n})
            for r in fixed:
                hist[self.profile.value(r)] += 1
            self.hist = hist
            self.count = (d + len(fixed)) // 2
        if sum(self.hist.values()) != self.count:
            raise ArithmeticError("component count/histogram mismatch")
        self.rebuilds += 1

    def label(self, r: int) -> int:
        r %= self.d
        return r if self.reflection is None else min(r, (self.reflection - r) % self.d)

    def weight(self, residue: int) -> Vector:
        r = residue % self.d
        out = self.profile.value(r)
        if self.reflection is not None:
            t = (self.reflection - r) % self.d
            if t != r:
                out = add(out, self.profile.value(t))
        return out

    def representative(self, weight: Vector, forbidden: set[int] | None = None) -> int | None:
        """A canonical residue with this weight, excluding named bulk orbits.

        The scan skips at most twice the number of forbidden labels; it never
        walks through a whole large fibre in the absence of explicit exclusions.
        """
        forbidden = set() if forbidden is None else forbidden
        blocked = set(forbidden)
        if self.reflection is None:
            profile = self.profile
        else:
            c, d = self.reflection, self.d
            fixed = fixed_residues(d, c)
            for x in fixed:
                if x not in forbidden and self.profile.value(x) == weight:
                    return x
            blocked.update(fixed)
            blocked.update((c - x) % d for x in forbidden)
            profile = self.folded
        for a, b, val in zip(profile.starts, profile.stops, profile.values):
            if val != weight:
                continue
            x = a
            while x < b and x in blocked:
                x += 1
            if x < b:
                return self.label(x)
        return None



class BulkIndex:
    """Prepared exact index; methods return no knot or manifold verdict."""
    def __init__(self, model: Model | dict[str, Any], check: Check = None):
        # Revalidate even directly constructed Model objects.
        self.model = Model.parse(model.as_dict() if isinstance(model, Model) else model)
        self.check = check
        self.version = 0
        self.added_edges: list[Edge] = []
        m = self.model
        adjacency: list[list[tuple[int, int, int, int]]] = [[] for _ in range(m.vertices)]
        for i, e in enumerate(m.edges):
            adjacency[e.u].append((e.v, e.sign, e.shift, i))
            adjacency[e.v].append((e.u, e.sign, (-e.sign * e.shift) % m.sheets, i))
        self.roots = [-1] * m.vertices
        self.signs = [1] * m.vertices
        self.shifts = [0] * m.vertices
        self.parents = [-1] * m.vertices
        for root in range(m.vertices):
            if self.roots[root] != -1:
                continue
            self.roots[root] = root
            queue = deque([root])
            while queue:
                if check:
                    check()
                u = queue.popleft()
                for v, sign, shift, eid in adjacency[u]:
                    if self.roots[v] != -1:
                        continue
                    self.roots[v] = root
                    self.signs[v] = sign * self.signs[u]
                    self.shifts[v] = (sign * self.shifts[u] + shift) % m.sheets
                    self.parents[v] = eid
                    queue.append(v)
        monodromies: dict[int, list[tuple[int, int]]] = {r: [] for r in set(self.roots)}
        for e in m.edges:
            r = self.roots[e.u]
            s = self.signs[e.v] * e.sign * self.signs[e.u]
            a = self.signs[e.v] * (e.sign * self.shifts[e.u] + e.shift - self.shifts[e.v])
            monodromies[r].append((s, a % m.sheets))
        records: dict[int, list[tuple[int, int, Vector]]] = {r: [] for r in monodromies}
        for w in m.weights:
            start = (w.start - self.shifts[w.v] if self.signs[w.v] == 1
                     else self.shifts[w.v] - w.stop + 1) % m.sheets
            records[self.roots[w.v]].append((start, w.stop - w.start, w.value))
        self.components: dict[int, Component] = {}
        self._hist: Counter = Counter()
        for root, maps in monodromies.items():
            c = next((a for s, a in maps if s == -1), None)
            d = m.sheets
            for s, a in maps:
                if check:
                    check()
                d = gcd(d, a if s == 1 else a - c)
            comp = Component(root, m.sheets, m.dimension, records[root], d,
                             None if c is None else c % d, check)
            self.components[root] = comp
            self._hist.update(comp.hist)

    @property
    def histogram(self) -> Counter:
        return self._hist.copy()

    @property
    def component_count(self) -> int:
        return sum(c.count for c in self.components.values())

    def key(self, vertex: int, sheet: int) -> Key:
        vertex, sheet = integer(vertex, "vertex"), integer(sheet, "sheet")
        m = self.model
        if not 0 <= vertex < m.vertices or not 0 <= sheet < m.sheets:
            raise ValueError("point outside input fibre system")
        root = self.roots[vertex]
        r = self.signs[vertex] * (sheet - self.shifts[vertex])
        return root, self.components[root].label(r)

    def key_weight(self, key: Key) -> Vector:
        return self.components[key[0]].weight(key[1])

    def weight(self, vertex: int, sheet: int) -> Vector:
        return self.key_weight(self.key(vertex, sheet))

    def representative(self, weight: Vector) -> Key | None:
        val = tuple(integer(x, "weight coordinate") for x in weight)
        if len(val) != self.model.dimension:
            raise ValueError("wrong weight dimension")
        for root, comp in self.components.items():
            x = comp.representative(val)
            if x is not None:
                return root, x
        return None

    def add_root_map(self, root: int, sign: int, shift: int) -> bool:
        """Add a full-fibre loop at an existing base root; fixed-base epoch only.

        Any effective change invalidates existing SparseOverlay objects. Call
        their rebase() method before further queries. No-op generators still
        enter the source model but leave the equivalence version unchanged.
        """
        root, sign, shift = integer(root), integer(sign), integer(shift)
        if root not in self.components or sign not in (-1, 1):
            raise ValueError("map must be a signed-affine loop at a base root")
        if self.check:
            self.check()
        m = self.model
        shift %= m.sheets
        comp = self.components[root]
        d, c = comp.d, comp.reflection
        if sign == 1:
            d = gcd(d, shift)
        elif c is None:
            c = shift % d
        else:
            d = gcd(d, shift - c)
        if c is not None:
            c %= d
        changed = (d, c) != (comp.d, comp.reflection)
        if changed:
            # Build off to the side: cooperative cancellation leaves the old
            # prepared state valid instead of partially changing its divisor.
            fresh = Component(root, m.sheets, m.dimension, comp.records, d, c, self.check)
            fresh.rebuilds = comp.rebuilds + 1
            for value, number in comp.hist.items():
                counter_change(self._hist, value, -number)
            self._hist.update(fresh.hist)
            self.components[root] = fresh
            self.version += 1
        self.added_edges.append(Edge(root, root, sign, shift))
        return changed

    def snapshot(self) -> Model:
        """Return the original model plus all accepted full-fibre additions."""
        m = self.model
        return Model(m.vertices, m.sheets, m.dimension,
                     m.edges + tuple(self.added_edges), m.weights)



class SparseOverlay:
    """Incremental pointwise gluing with optional additive edge payloads."""
    def __init__(self, index: BulkIndex):
        self.index = index
        self.defects: list[Defect] = []
        self._reset()

    def _reset(self) -> None:
        self.version = self.index.version
        self.hist = self.index.histogram
        self.count = self.index.component_count
        self.parent: dict[Key, Key] = {}
        self.size: dict[Key, int] = {}
        self.weights: dict[Key, Vector] = {}

    def _fresh(self) -> None:
        if self.version != self.index.version:
            raise RuntimeError("bulk equivalence changed; call rebase()")

    def _find(self, key: Key) -> Key:
        root = key
        while self.parent[root] != root:
            root = self.parent[root]
        while self.parent[key] != key:
            nxt = self.parent[key]
            self.parent[key] = root
            key = nxt
        return root

    def _touch(self, key: Key) -> None:
        if key not in self.parent:
            self.parent[key] = key
            self.size[key] = 1
            self.weights[key] = self.index.key_weight(key)

    def _apply(self, edge: Defect) -> None:
        a = self.index.key(edge.u, edge.x)
        b = self.index.key(edge.v, edge.y)
        self._touch(a)
        self._touch(b)
        a, b = self._find(a), self._find(b)
        counter_change(self.hist, self.weights[a], -1)
        if a != b:
            counter_change(self.hist, self.weights[b], -1)
            if self.size[a] < self.size[b]:
                a, b = b, a
            self.parent[b] = a
            self.size[a] += self.size[b]
            self.weights[a] = add(self.weights[a], self.weights[b])
            del self.weights[b]
            self.count -= 1
        self.weights[a] = add(self.weights[a], edge.payload)
        self.hist[self.weights[a]] += 1

    def add(self, defect: Defect | dict[str, Any]) -> None:
        self._fresh()
        if self.index.check:
            self.index.check()
        d = parse_defect(vars(defect) if isinstance(defect, Defect) else defect,
                         self.index.model)
        self._apply(d)
        self.defects.append(d)

    def rebase(self) -> None:
        """Replay saved endpoints after a bulk coarsening; never reuse old labels."""
        # Prepare separately: cancellation must not expose a partial replay.
        fresh = SparseOverlay(self.index)
        for edge in self.defects:
            if self.index.check:
                self.index.check()
            fresh._apply(edge)
        self.version = fresh.version
        self.hist, self.count = fresh.hist, fresh.count
        self.parent, self.size, self.weights = fresh.parent, fresh.size, fresh.weights

    @property
    def histogram(self) -> Counter:
        self._fresh()
        return self.hist.copy()

    @property
    def component_count(self) -> int:
        self._fresh()
        return self.count

    def weight(self, vertex: int, sheet: int) -> Vector:
        self._fresh()
        key = self.index.key(vertex, sheet)
        return self.weights[self._find(key)] if key in self.parent else self.index.key_weight(key)

    def representative(self, weight: Vector) -> Key | None:
        self._fresh()
        val = tuple(integer(x, "weight coordinate") for x in weight)
        if len(val) != self.index.model.dimension:
            raise ValueError("wrong weight dimension")
        if val not in self.hist:
            return None
        for key, w in self.weights.items():
            if w == val:
                return key
        forbidden: dict[int, set[int]] = {}
        for root, x in self.parent:
            forbidden.setdefault(root, set()).add(x)
        for root, comp in self.index.components.items():
            x = comp.representative(val, forbidden.get(root, set()))
            if x is not None:
                return root, x
        raise ArithmeticError("histogram has no representative")

    def same_component(self, u: int, x: int, v: int, y: int) -> bool:
        self._fresh()
        a, b = self.index.key(u, x), self.index.key(v, y)
        if a == b:
            return True
        return a in self.parent and b in self.parent and self._find(a) == self._find(b)


def histogram_records(hist: Counter) -> list[dict[str, Any]]:
    return [{"weight": list(w), "multiplicity": n} for w, n in sorted(hist.items())]
