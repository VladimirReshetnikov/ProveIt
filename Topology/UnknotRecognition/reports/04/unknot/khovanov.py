"""An exact EXPONENTIAL unknot recognizer, not the quasi-polynomial algorithm.

Builds the reduced Khovanov complex over F2 and computes its total homology
rank. A validated classical knot is the unknot exactly when this rank is one.
See docs/report.pdf for the theorem dependencies and actual complexity.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from time import monotonic
from typing import Any, Iterator
import math

from .diagram import Diagram, DisjointSet
from .linear import apply_matrix, rank_f2


class ResourceLimit(RuntimeError):
    """A requested resource budget was exhausted; this is NOT a knot verdict."""


class InternalInvariantError(RuntimeError):
    """An algebraic invariant failed; no knot verdict is returned."""


@dataclass(frozen=True)
class Limits:
    max_states: int | None = None
    max_generators: int | None = None
    seconds: float | None = None

    def __post_init__(self) -> None:
        for name in ("max_states", "max_generators"):
            value = getattr(self, name)
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError(f"{name} must be a nonnegative integer or None")
        if self.seconds is not None:
            try:
                valid = (type(self.seconds) in (int, float) and
                         math.isfinite(self.seconds) and self.seconds >= 0)
            except OverflowError:
                valid = False
            if not valid:
                raise ValueError("seconds must be finite and nonnegative or None")


@dataclass
class Budget:
    limits: Limits
    start: float = field(default_factory=monotonic)
    states: int = 0
    generators: int = 0

    def tick(self) -> None:
        if self.limits.seconds is not None:
            if monotonic() - self.start >= self.limits.seconds:
                raise ResourceLimit("wall-clock budget reached (cooperative check)")

    def add(self, dimension: int) -> None:
        self.tick()
        if (self.limits.max_generators is not None and
                self.generators + dimension > self.limits.max_generators):
            raise ResourceLimit("enhanced-state generator budget reached")
        self.states += 1
        self.generators += dimension


@dataclass(frozen=True)
class Resolution:
    state: int
    degree: int
    circles: tuple[tuple[int, ...], ...]
    edge_to_circle: tuple[int, ...]
    marked_circle: int
    dimension: int
    offset: int

    def full_labels(self, compact: int) -> int:
        """Insert the mandatory X label on the marked circle."""
        p = self.marked_circle
        return (compact & ((1 << p) - 1)) | (1 << p) | ((compact >> p) << (p + 1))

    def compact_labels(self, full: int) -> int:
        p = self.marked_circle
        if not ((full >> p) & 1):
            raise InternalInvariantError("differential left the reduced subcomplex")
        return (full & ((1 << p) - 1)) | ((full >> (p + 1)) << p)


def resolve(diagram: Diagram, state: int, offset: int = 0) -> Resolution:
    n = diagram.crossings
    if n == 0 or not 0 <= state < (1 << n):
        raise ValueError("resolve requires a nonempty diagram and a valid state")
    union = DisjointSet(diagram.edges)
    for i, (a, b, c, d) in enumerate(diagram.pd):
        if (state >> i) & 1:
            union.union(a, d)
            union.union(b, c)
        else:
            union.union(a, b)
            union.union(c, d)
    roots: dict[int, int] = {}
    groups: list[list[int]] = []
    mapping = []
    for edge in range(diagram.edges):
        root = union.find(edge)
        if root not in roots:
            roots[root] = len(groups)
            groups.append([])
        index = roots[root]
        groups[index].append(edge)
        mapping.append(index)
    k = len(groups)
    if k > n + 1:
        raise InternalInvariantError("too many resolution circles for a knot diagram")
    return Resolution(state, state.bit_count(), tuple(map(tuple, groups)), tuple(mapping),
                      mapping[diagram.basepoint], 1 << (k - 1), offset)


@dataclass(frozen=True)
class Saddle:
    """A merge or split map between adjacent resolutions."""
    target: Resolution
    unchanged: tuple[tuple[int, int], ...]
    source_changed: tuple[int, ...]
    target_changed: tuple[int, ...]

    @classmethod
    def between(cls, source: Resolution, target: Resolution) -> Saddle:
        if source.degree + 1 != target.degree:
            raise InternalInvariantError("incorrect saddle degree")
        destinations = [tuple(sorted({target.edge_to_circle[e] for e in circle}))
                        for circle in source.circles]
        preimages: list[list[int]] = [[] for _ in target.circles]
        for i, images in enumerate(destinations):
            for j in images:
                preimages[j].append(i)
        unchanged = []
        for i, images in enumerate(destinations):
            if len(images) == 1 and len(preimages[images[0]]) == 1:
                unchanged.append((i, images[0]))
        unchanged_source = {i for i, _ in unchanged}
        unchanged_target = {j for _, j in unchanged}
        source_changed = tuple(i for i in range(len(source.circles))
                               if i not in unchanged_source)
        target_changed = tuple(j for j in range(len(target.circles))
                               if j not in unchanged_target)
        shape = (len(source_changed), len(target_changed))
        if shape not in ((2, 1), (1, 2)):
            raise InternalInvariantError(f"resolution edge is not a saddle: {shape}")
        return cls(target, tuple(unchanged), source_changed, target_changed)

    def images(self, full: int) -> tuple[int, ...]:
        """Target compact basis indices; coefficients are all 1 over F2."""
        target_labels = 0
        for i, j in self.unchanged:
            if (full >> i) & 1:
                target_labels |= 1 << j
        if len(self.source_changed) == 2:
            a, b = self.source_changed
            x, y = (full >> a) & 1, (full >> b) & 1
            if x and y:  # m(X,X) = 0
                return ()
            if x or y:
                target_labels |= 1 << self.target_changed[0]
            return (self.target.compact_labels(target_labels),)
        a = self.source_changed[0]
        b, c = self.target_changed
        if (full >> a) & 1:  # Delta(X) = X tensor X
            return (self.target.compact_labels(target_labels | (1 << b) | (1 << c)),)
        # Delta(1) = 1 tensor X + X tensor 1
        return (self.target.compact_labels(target_labels | (1 << b)),
                self.target.compact_labels(target_labels | (1 << c)))


@dataclass
class Complex:
    diagram: Diagram
    resolutions: list[Resolution]
    by_degree: list[list[Resolution]]
    dimensions: list[int]
    budget: Budget

    @classmethod
    def build(cls, diagram: Diagram, budget: Budget) -> Complex:
        n = diagram.crossings
        if n == 0:
            budget.tick()
            if budget.limits.max_states is not None and budget.limits.max_states < 1:
                raise ResourceLimit("resolution-state budget reached")
            budget.add(1)
            return cls(diagram, [], [[]], [1], budget)
        if (budget.limits.max_states is not None and
                (1 << n) > budget.limits.max_states):
            raise ResourceLimit(f"requires 2**{n} resolutions; max_states exceeded")
        resolutions = []
        by_degree: list[list[Resolution]] = [[] for _ in range(n + 1)]
        dimensions = [0] * (n + 1)
        for state in range(1 << n):
            budget.tick()
            h = state.bit_count()
            r = resolve(diagram, state, dimensions[h])
            budget.add(r.dimension)
            dimensions[h] += r.dimension
            by_degree[h].append(r)
            resolutions.append(r)
        return cls(diagram, resolutions, by_degree, dimensions, budget)

    def columns(self, degree: int) -> Iterator[int]:
        """Stream d_degree columns; rows indexed within C_(degree+1)."""
        n = self.diagram.crossings
        if not 0 <= degree < n:
            raise ValueError("differential degree out of range")
        for source in self.by_degree[degree]:
            self.budget.tick()
            saddles = [Saddle.between(source, self.resolutions[source.state | (1 << i)])
                       for i in range(n) if not ((source.state >> i) & 1)]
            for compact in range(source.dimension):
                self.budget.tick()
                full = source.full_labels(compact)
                column = 0
                for saddle in saddles:
                    for image in saddle.images(full):
                        column ^= 1 << (saddle.target.offset + image)
                yield column

    def compute(self, verify_d2: bool = False) -> tuple[list[int], list[int]]:
        n = self.diagram.crossings
        ranks = []
        previous: list[int] | None = None
        for h in range(n):
            if verify_d2:
                current = list(self.columns(h))
                if previous is not None:
                    for column in previous:
                        self.budget.tick()
                        if apply_matrix(current, column):
                            raise InternalInvariantError("d_(h+1) d_h is not zero")
                ranks.append(rank_f2(current, self.dimensions[h + 1], self.budget.tick))
                previous = current
            else:
                ranks.append(rank_f2(self.columns(h), self.dimensions[h + 1],
                                     self.budget.tick))
        homology = [self.dimensions[h] - (ranks[h - 1] if h else 0)
                    - (ranks[h] if h < n else 0) for h in range(n + 1)]
        if any(b < 0 for b in homology):
            raise InternalInvariantError("negative homology dimension")
        return ranks, homology


@dataclass(frozen=True)
class Result:
    status: str
    crossings: int
    reduced_rank: int | None
    chain_dimensions: tuple[int, ...]
    differential_ranks: tuple[int, ...]
    homology_dimensions: tuple[int, ...]
    states_built: int
    generators_built: int
    elapsed_seconds: float
    verified_d2: bool
    reason: str | None = None

    def to_json(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "algorithm": "reduced-khovanov-f2",
            "worst_case_bound": "2^{O(n)}; NOT n^{O(log n)}",
            "quasipolynomial_guarantee": False,
            "crossings": self.crossings,
            "reduced_khovanov_rank_f2": self.reduced_rank,
            "chain_dimensions_by_cube_degree": list(self.chain_dimensions),
            "differential_ranks_by_cube_degree": list(self.differential_ranks),
            "homology_dimensions_by_cube_degree": list(self.homology_dimensions),
            "states_built": self.states_built,
            "generators_built": self.generators_built,
            "elapsed_seconds": self.elapsed_seconds,
            "verified_d_squared_zero": self.verified_d2,
            "reason": self.reason,
        }


def recognize(diagram: Diagram, limits: Limits | None = None,
              verify_d2: bool = False) -> Result:
    """Decide exactly unless a resource limit is reached, then return UNKNOWN.

    Invalid or nonclassical input raises DiagramError. No heuristic inference
    from a timeout, determinant, Jones polynomial, or Alexander polynomial.
    """
    if not isinstance(diagram, Diagram):
        raise TypeError("diagram must be a Diagram")
    if limits is not None and not isinstance(limits, Limits):
        raise TypeError("limits must be a Limits object or None")
    if type(verify_d2) is not bool:
        raise TypeError("verify_d2 must be a bool")
    # Never trust a manually constructed dataclass instance.
    diagram = Diagram.from_pd(diagram.pd, diagram.basepoint)
    budget = Budget(limits or Limits())
    try:
        complex_ = Complex.build(diagram, budget)
        ranks, homology = complex_.compute(verify_d2)
        rank = sum(homology)
        if rank < 1 or rank % 2 != 1:
            raise InternalInvariantError("a knot must have positive odd reduced F2 rank")
        return Result("UNKNOT" if rank == 1 else "KNOTTED", diagram.crossings,
                      rank, tuple(complex_.dimensions), tuple(ranks), tuple(homology),
                      budget.states, budget.generators, monotonic() - budget.start,
                      verify_d2)
    except (ResourceLimit, MemoryError) as exc:
        return Result("UNKNOWN", diagram.crossings, None, (), (), (), budget.states,
                      budget.generators, monotonic() - budget.start, False,
                      str(exc) or "memory allocation failed")
