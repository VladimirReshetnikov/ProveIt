"""An exact reduced Khovanov complex over F_2, NOT a QP implementation.

Tensor basis: bit 0 means 1, bit 1 means x in F_2[x]/(x*x).
The component containing the marked edge is constrained to carry x.
We compute total rank, so orientation-dependent grading shifts are unnecessary.
"""
from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass
from typing import Iterator

from .algebra import DisjointSet, rank_f2
from .diagram import PlanarDiagram


class ResourceLimit(RuntimeError):
    """A resource cap was reached. This is UNKNOWN, never a knot verdict."""


@dataclass(frozen=True)
class Resolution:
    state: int
    circles: tuple[int, ...]  # bitsets of original edge labels, marked circle first
    offset: int

    @property
    def dimension(self) -> int:
        return 1 << (len(self.circles) - 1)


@dataclass(frozen=True)
class Saddle:
    target_state: int
    unchanged: tuple[tuple[int, int], ...]
    source_active: tuple[int, ...]
    target_active: tuple[int, ...]

    def images(self, reduced_bits: int) -> tuple[int, ...]:
        """Return the nonzero target basis vectors; all coefficients are one."""
        full = (reduced_bits << 1) | 1
        result = 0
        for source, target in self.unchanged:
            result |= ((full >> source) & 1) << target
        if len(self.source_active) == 2:  # multiplication / merge
            a, b = self.source_active
            count = ((full >> a) & 1) + ((full >> b) & 1)
            if count == 2:
                return ()
            result |= count << self.target_active[0]
            if not result & 1:
                raise ArithmeticError("Reduced subcomplex not preserved by multiplication.")
            return (result >> 1,)
        # comultiplication / split: Delta(1)=1*x+x*1, Delta(x)=x*x
        a = self.source_active[0]
        b, c = self.target_active
        if (full >> a) & 1:
            result |= (1 << b) | (1 << c)
            if not result & 1:
                raise ArithmeticError("Reduced subcomplex not preserved by comultiplication.")
            return (result >> 1,)
        first, second = result | (1 << b), result | (1 << c)
        if not first & 1 or not second & 1:
            raise ArithmeticError("The marked circle cannot split while labelled 1.")
        return (first >> 1, second >> 1)


@dataclass(frozen=True)
class KhovanovResult:
    chain_dimensions: tuple[int, ...]
    differential_ranks: tuple[int, ...]
    homology_dimensions: tuple[int, ...]
    resolutions: int
    total_basis: int
    d_squared_checked: bool

    @property
    def total_rank(self) -> int:
        return sum(self.homology_dimensions)

    def to_json(self) -> dict:
        return {
            "field": "F2", "reduced": True,
            "grading": "unnormalized cube degree; total rank is normalized-invariant",
            "chain_dimensions": list(self.chain_dimensions),
            "differential_ranks": list(self.differential_ranks),
            "homology_dimensions": list(self.homology_dimensions),
            "total_rank": self.total_rank,
            "resolutions": self.resolutions, "total_basis": self.total_basis,
            "d_squared_checked": self.d_squared_checked,
        }


class ReducedComplex:
    def __init__(self, diagram: PlanarDiagram, *, marked_edge: int = 0,
                 max_resolutions: int | None = None, max_basis: int | None = None):
        for name, cap in (("max_resolutions", max_resolutions), ("max_basis", max_basis)):
            if cap is not None and (type(cap) is not int or cap < 1):
                raise ValueError(f"{name} must be a positive integer or None.")
        if type(marked_edge) is not int or not 0 <= marked_edge < max(1, 2 * diagram.n):
            raise ValueError("Marked edge is out of range.")
        self.diagram = diagram
        self.marked_edge = marked_edge
        count = 1 << diagram.n
        if max_resolutions is not None and count > max_resolutions:
            raise ResourceLimit(f"Need 2^{diagram.n} resolutions; cap is {max_resolutions}.")
        self.by_degree: list[list[Resolution]] = [[] for _ in range(diagram.n + 1)]
        self.dimensions = [0] * (diagram.n + 1)
        self.resolutions: list[Resolution] = []
        total = 0
        for state in range(count):
            circles = self._circles(state)
            degree = state.bit_count()
            resolution = Resolution(state, circles, self.dimensions[degree])
            total += resolution.dimension
            if max_basis is not None and total > max_basis:
                raise ResourceLimit(f"The reduced chain basis exceeds cap {max_basis}.")
            self.dimensions[degree] += resolution.dimension
            self.by_degree[degree].append(resolution)
            self.resolutions.append(resolution)
        self.total_basis = total
        self._saddles: dict[int, tuple[Saddle, ...]] = {}
        self._degree_offsets = [[r.offset for r in rows] for rows in self.by_degree]

    def _circles(self, state: int) -> tuple[int, ...]:
        n = self.diagram.n
        if not n:
            return (1,)
        dsu = DisjointSet(2 * n)
        for i, (a, b, c, d) in enumerate(self.diagram.crossings):
            if (state >> i) & 1:
                dsu.union(a, d)
                dsu.union(b, c)
            else:
                dsu.union(a, b)
                dsu.union(c, d)
        groups: dict[int, int] = {}
        for edge in range(2 * n):
            root = dsu.find(edge)
            groups[root] = groups.get(root, 0) | (1 << edge)
        mark = 1 << self.marked_edge
        return tuple(sorted(groups.values(), key=lambda mask: (not bool(mask & mark), mask)))

    def saddles(self, state: int) -> tuple[Saddle, ...]:
        if state in self._saddles:
            return self._saddles[state]
        source = self.resolutions[state]
        result = []
        for crossing in range(self.diagram.n):
            if (state >> crossing) & 1:
                continue
            target_state = state | (1 << crossing)
            target = self.resolutions[target_state]
            target_index = {mask: i for i, mask in enumerate(target.circles)}
            unchanged = tuple((i, target_index[mask]) for i, mask in enumerate(source.circles)
                              if mask in target_index)
            fixed_sources = {i for i, j in unchanged}
            fixed_targets = {j for i, j in unchanged}
            active_sources = tuple(i for i in range(len(source.circles)) if i not in fixed_sources)
            active_targets = tuple(j for j in range(len(target.circles)) if j not in fixed_targets)
            if (len(active_sources), len(active_targets)) not in ((2, 1), (1, 2)):
                raise ArithmeticError("A classical saddle must merge two circles or split one.")
            source_union = 0
            target_union = 0
            for i in active_sources:
                source_union |= source.circles[i]
            for j in active_targets:
                target_union |= target.circles[j]
            if source_union != target_union:
                raise ArithmeticError("Saddle has inconsistent edge support.")
            result.append(Saddle(target_state, unchanged, active_sources, active_targets))
        self._saddles[state] = tuple(result)
        return self._saddles[state]

    def column(self, state: int, reduced_bits: int) -> int:
        resolution = self.resolutions[state]
        if not 0 <= reduced_bits < resolution.dimension:
            raise ValueError("Tensor basis index out of range.")
        result = 0
        for saddle in self.saddles(state):
            target = self.resolutions[saddle.target_state]
            for image in saddle.images(reduced_bits):
                result ^= 1 << (target.offset + image)
        return result

    def columns(self, degree: int) -> Iterator[int]:
        for resolution in self.by_degree[degree]:
            for bits in range(resolution.dimension):
                yield self.column(resolution.state, bits)

    def basis_at(self, degree: int, index: int) -> tuple[int, int]:
        if not 0 <= index < self.dimensions[degree]:
            raise ValueError("Chain basis index out of range.")
        resolution_index = bisect_right(self._degree_offsets[degree], index) - 1
        resolution = self.by_degree[degree][resolution_index]
        return resolution.state, index - resolution.offset

    def check_d_squared(self) -> None:
        """Exhaustively check d*d=0 on each basis vector (optional, exponential)."""
        for degree in range(self.diagram.n - 1):
            for column in self.columns(degree):
                image = 0
                while column:
                    low = column & -column
                    index = low.bit_length() - 1
                    state, bits = self.basis_at(degree + 1, index)
                    image ^= self.column(state, bits)
                    column ^= low
                if image:
                    raise ArithmeticError("Khovanov differential failed d*d=0.")

    def compute(self, *, check_d_squared: bool = False) -> KhovanovResult:
        if check_d_squared:
            self.check_d_squared()
        euler = sum((-1) ** k * d for k, d in enumerate(self.dimensions))
        if abs(euler) != 1:
            raise ArithmeticError("The reduced knot complex must have Euler characteristic +/-1.")
        ranks = [rank_f2(self.columns(k)) for k in range(self.diagram.n)] + [0]
        homology = [dimension - ranks[k] - (ranks[k - 1] if k else 0)
                    for k, dimension in enumerate(self.dimensions)]
        if any(dimension < 0 for dimension in homology):
            raise ArithmeticError("Negative homology dimension.")
        return KhovanovResult(tuple(self.dimensions), tuple(ranks), tuple(homology),
                              len(self.resolutions), self.total_basis, check_d_squared)
