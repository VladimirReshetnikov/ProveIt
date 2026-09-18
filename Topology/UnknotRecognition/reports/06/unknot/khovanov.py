"""Exact reduced Khovanov homology over F_2, with an exponential bound.

No claim of a quasipolynomial worst-case running time is made by this module.
The marked resolution circle is fixed to x in F_2[x]/(x^2). Grading shifts
are omitted because only the total dimension is used for recognition.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
from typing import Any, Iterator

from .diagram import Diagram, DisjointSet, popcount
from .limits import Budget, BudgetExceeded, Limits
from .linear import rank_f2


@dataclass(frozen=True)
class Resolution:
    circle_of: tuple[int, ...]
    circles: tuple[tuple[int, ...], ...]

    @property
    def dimension(self) -> int:
        return 1 << (len(self.circles) - 1)


def resolve(diagram: Diagram, state: int) -> Resolution:
    """Zero smoothing: (a,b),(c,d); one smoothing: (a,d),(b,c)."""
    n = diagram.crossings
    if not 0 <= state < 1 << n:
        raise ValueError("Resolution state is out of range")
    if n == 0:
        return Resolution((0,), ((0,),))
    connected = DisjointSet(2 * n)
    for crossing, (a, b, c, d) in enumerate(diagram.pd):
        if state >> crossing & 1:
            connected.union(a, d)
            connected.union(b, c)
        else:
            connected.union(a, b)
            connected.union(c, d)
    roots: dict[int, int] = {}
    circles: list[list[int]] = []
    circle_of = []
    for edge in range(2 * n):
        root = connected.find(edge)
        if root not in roots:
            roots[root] = len(circles)
            circles.append([])
        index = roots[root]
        circles[index].append(edge)
        circle_of.append(index)
    # The basepoint edge zero always belongs to circle zero.
    return Resolution(tuple(circle_of), tuple(tuple(c) for c in circles))


@dataclass(frozen=True)
class Saddle:
    unchanged: tuple[tuple[int, int], ...]
    sources: tuple[int, ...]
    targets: tuple[int, ...]

    @classmethod
    def between(cls, source: Resolution, target: Resolution) -> Saddle:
        target_index = {circle: i for i, circle in enumerate(target.circles)}
        unchanged = tuple((i, target_index[circle])
                          for i, circle in enumerate(source.circles) if circle in target_index)
        used_source = {a for a, _ in unchanged}
        used_target = {b for _, b in unchanged}
        sources = tuple(i for i in range(len(source.circles)) if i not in used_source)
        targets = tuple(i for i in range(len(target.circles)) if i not in used_target)
        if (len(sources), len(targets)) not in ((2, 1), (1, 2)):
            raise ArithmeticError("A classical cube edge must merge two circles or split one")
        return cls(unchanged, sources, targets)

    def image(self, compact_labels: int) -> tuple[int, ...]:
        """Images of a reduced generator, with bit 1 representing x.

        m(1,1)=1, m(1,x)=m(x,1)=x, m(x,x)=0;
        Delta(1)=1*x + x*1, Delta(x)=x*x.
        The leading marked-circle x is inserted and removed explicitly.
        """
        labels = (compact_labels << 1) | 1
        output = 0
        for source, target in self.unchanged:
            output |= ((labels >> source) & 1) << target
        if len(self.sources) == 2:
            a, b = self.sources
            x, y = (labels >> a) & 1, (labels >> b) & 1
            if x and y:
                return ()
            expanded = (output | ((x | y) << self.targets[0]),)
        else:
            x = (labels >> self.sources[0]) & 1
            a, b = self.targets
            expanded = ((output | (1 << a) | (1 << b),) if x else
                        (output | (1 << a), output | (1 << b)))
        if any(not value & 1 for value in expanded):
            raise ArithmeticError("Differential left the marked-x reduced subcomplex")
        return tuple(value >> 1 for value in expanded)


class Complex:
    """Resolution cube with streaming differential columns.

    Space use includes all resolutions but not all differential matrices.
    No topology library or online service is consulted.
    """
    def __init__(self, diagram: Diagram, budget: Budget | None = None) -> None:
        # Normalize even directly constructed Diagram values and preserve edge 0.
        self.diagram = Diagram.from_pd(diagram.pd, name=diagram.name)
        self.budget = budget or Budget()
        self.n = self.diagram.crossings
        count = 1 << self.n
        self.budget.states(count)
        self.resolutions: list[Resolution] = []
        self.states_by_height: list[list[int]] = [[] for _ in range(self.n + 1)]
        self.offsets = [0] * count
        self.chain_dimensions = [0] * (self.n + 1)
        total = 0
        for state in range(count):
            self.budget.check()
            resolution = resolve(self.diagram, state)
            height = popcount(state)
            self.offsets[state] = self.chain_dimensions[height]
            self.chain_dimensions[height] += resolution.dimension
            total += resolution.dimension
            self.budget.generators(total)
            self.resolutions.append(resolution)
            self.states_by_height[height].append(state)
        self.total_generators = total

    def edges(self, state: int) -> tuple[tuple[int, Saddle], ...]:
        return tuple((state | (1 << crossing), Saddle.between(
            self.resolutions[state], self.resolutions[state | (1 << crossing)]))
            for crossing in range(self.n) if not state >> crossing & 1)

    def basis_image(self, state: int, labels: int,
                    edges: tuple[tuple[int, Saddle], ...] | None = None) -> int:
        result = 0
        for target, saddle in self.edges(state) if edges is None else edges:
            offset = self.offsets[target]
            for image in saddle.image(labels):
                if image >= self.resolutions[target].dimension:
                    raise ArithmeticError("Saddle produced an invalid basis index")
                result ^= 1 << (offset + image)
        return result

    def columns(self, height: int) -> Iterator[int]:
        if not 0 <= height <= self.n:
            raise ValueError("Homological degree out of range")
        for state in self.states_by_height[height]:
            edges = self.edges(state)
            for labels in range(self.resolutions[state].dimension):
                self.budget.check()
                yield self.basis_image(state, labels, edges)

    def check_d_squared(self) -> bool:
        """Exhaustively check d*d=0 on every generator, not a random sample.

        This diagnostic materializes consecutive matrices and can use more
        memory than the normal streaming computation. It is optional.
        """
        previous = list(self.columns(0))
        for height in range(1, self.n + 1):
            following = list(self.columns(height))
            for column in previous:
                product = 0
                while column:
                    self.budget.check()
                    low = column & -column
                    product ^= following[low.bit_length() - 1]
                    column ^= low
                if product:
                    return False
            previous = following
        return True

    def homology(self) -> tuple[list[int], list[int]]:
        ranks = [rank_f2(self.columns(h), budget=self.budget) for h in range(self.n)]
        ranks.append(0)
        betti = [dimension - ranks[h] - (ranks[h - 1] if h else 0)
                 for h, dimension in enumerate(self.chain_dimensions)]
        if any(value < 0 for value in betti) or sum(betti) < 1:
            raise ArithmeticError("Invalid homology dimensions; computation invariant failed")
        return ranks, betti


def recognize(diagram: Diagram, *, limits: Limits | None = None,
              check_d_squared: bool = False) -> dict[str, Any]:
    """Decide unknotness exactly, or return unknown if a requested budget expires.

    With no budget this is a total, exponential-time algorithm on validated
    classical knot inputs. Resource exhaustion does NOT certify knottedness.
    """
    # Validation failures are exceptions, not mathematical answers.
    diagram = Diagram.from_pd(diagram.pd, name=diagram.name)
    budget = Budget(limits)
    result: dict[str, Any] = {
        "schema": "unknot-result-v1",
        "algorithm": "reduced-khovanov-f2",
        "worst_case": "2^O(n); NOT n^O(log n)",
        "input": diagram.to_json(),
        "crossings": diagram.crossings,
        "coefficient_field": "F_2",
        "grading": "unnormalized cube height; writhe shifts omitted",
    }
    try:
        complex_ = Complex(diagram, budget)
        result.update(resolutions=len(complex_.resolutions),
                      total_generators=complex_.total_generators,
                      chain_dimensions=complex_.chain_dimensions)
        if check_d_squared:
            if not complex_.check_d_squared():
                raise ArithmeticError("Differential does not square to zero")
            result["d_squared_checked"] = True
        else:
            result["d_squared_checked"] = False
        ranks, betti = complex_.homology()
        total = sum(betti)
        result.update(status="unknot" if total == 1 else "knotted",
                      differential_ranks=ranks, betti_by_height=betti,
                      reduced_homology_dimension=total)
    except BudgetExceeded as error:
        result.update(status="unknown", reason=str(error))
    result["elapsed_seconds"] = round(budget.elapsed, 6)
    return result


def verify_report(report: dict[str, Any], *, limits: Limits | None = None) -> bool:
    """Recompute a report. This is NOT a short or independent proof certificate.

    It checks every reported algebraic datum and exhaustively checks d^2=0.
    Its cost can exceed that of the original computation.
    """
    if report.get("schema") != "unknot-result-v1" or report.get("status") not in (
            "unknot", "knotted"):
        return False
    try:
        diagram = Diagram.from_json(report["input"])
        actual = recognize(diagram, limits=limits, check_d_squared=True)
        keys = ("algorithm", "worst_case", "crossings", "coefficient_field", "grading",
                "resolutions", "total_generators", "chain_dimensions", "differential_ranks",
                "betti_by_height", "reduced_homology_dimension", "status")
        return actual["status"] != "unknown" and all(
            json.dumps(report.get(k), sort_keys=True, allow_nan=False) ==
            json.dumps(actual[k], sort_keys=True, allow_nan=False) for k in keys)
    except (ValueError, TypeError, KeyError):
        return False
