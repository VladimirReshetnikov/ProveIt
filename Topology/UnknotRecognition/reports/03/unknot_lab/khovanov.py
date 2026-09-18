"""Reduced Khovanov homology over F2 by explicit cube enumeration.

This is a complete exact REFERENCE algorithm when run without resource
limits. It is exponential, NOT the hierarchy algorithm in the supplied notes.
It does not compute just the Jones polynomial. It computes differential ranks.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator

from .diagrams import PlanarDiagram, UnionFind
from .linear import determinant_bareiss, rank_f2


class ResourceLimit(RuntimeError):
    """A resource ceiling stopped a computation; the answer is UNKNOWN."""


@dataclass(frozen=True)
class Limits:
    states: int | None = 65536
    generators: int | None = 200000
    matrix_bits: int | None = 128000000

    def __post_init__(self) -> None:
        for value in (self.states, self.generators, self.matrix_bits):
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError("Resource ceilings must be positive integers or None")


@dataclass(frozen=True)
class Resolution:
    components: tuple[tuple[int, ...], ...]
    owner: tuple[int, ...]
    base: int
    free: tuple[int, ...]
    degree: int
    offset: int

    @property
    def dimension(self) -> int:
        return 1 << len(self.free)

    def decode(self, code: int) -> list[int]:
        labels = [0] * len(self.components)
        labels[self.base] = 1  # Label x, not the algebra unit.
        for bit, circle in enumerate(self.free):
            labels[circle] = (code >> bit) & 1
        return labels

    def encode(self, labels: list[int]) -> int | None:
        if labels[self.base] != 1:
            return None
        return sum(labels[circle] << bit for bit, circle in enumerate(self.free))


@dataclass(frozen=True)
class Saddle:
    target_state: int
    unchanged: tuple[tuple[int, int], ...]
    source_changed: tuple[int, ...]
    target_changed: tuple[int, ...]

    def images(self, labels: list[int], target: Resolution) -> Iterator[int]:
        out = [0] * len(target.components)
        for source_circle, target_circle in self.unchanged:
            out[target_circle] = labels[source_circle]
        if len(self.source_changed) == 2:  # Multiplication.
            a, b = (labels[i] for i in self.source_changed)
            if a and b:  # x*x = 0.
                return
            out[self.target_changed[0]] = a | b
            encoded = target.encode(out)
            if encoded is not None:
                yield encoded
        else:  # Comultiplication.
            a = labels[self.source_changed[0]]
            choices = ((1, 1),) if a else ((0, 1), (1, 0))
            j, k = self.target_changed
            for left, right in choices:
                out[j], out[k] = left, right
                encoded = target.encode(out)
                if encoded is not None:
                    yield encoded


def smoothing(pd: PlanarDiagram, state: int, base_edge: int,
              offset: int) -> Resolution:
    uf = UnionFind(2 * pd.n)
    for crossing, (a, b, c, d) in enumerate(pd.crossings):
        if state >> crossing & 1:
            uf.union(a, d)
            uf.union(b, c)
        else:
            uf.union(a, b)
            uf.union(c, d)
    groups: dict[int, list[int]] = {}
    for edge in range(2 * pd.n):
        groups.setdefault(uf.find(edge), []).append(edge)
    components = tuple(sorted(tuple(g) for g in groups.values()))
    owner = [0] * (2 * pd.n)
    for circle, edges in enumerate(components):
        for edge in edges:
            owner[edge] = circle
    base = owner[base_edge]
    return Resolution(components, tuple(owner), base,
                      tuple(i for i in range(len(components)) if i != base),
                      state.bit_count(), offset)


def make_saddle(source: Resolution, target: Resolution, state: int) -> Saddle:
    source_sets = {edges: i for i, edges in enumerate(source.components)}
    target_sets = {edges: i for i, edges in enumerate(target.components)}
    unchanged = tuple((i, target_sets[edges]) for edges, i in source_sets.items()
                      if edges in target_sets)
    source_changed = tuple(i for edges, i in source_sets.items() if edges not in target_sets)
    target_changed = tuple(i for edges, i in target_sets.items() if edges not in source_sets)
    if (len(source_changed), len(target_changed)) not in ((2, 1), (1, 2)):
        raise ArithmeticError("A classical smoothing edge must be a merge or split")
    return Saddle(state, unchanged, source_changed, target_changed)


class CubeComplex:
    def __init__(self, pd: PlanarDiagram, base_edge: int = 0,
                 limits: Limits = Limits()):
        if pd.n == 0:
            raise ValueError("The crossing-free circle is handled directly")
        # Validate a directly provided base edge before using it for array access.
        if type(base_edge) is not int or not 0 <= base_edge < 2 * pd.n:
            raise ValueError("Invalid internal basepoint edge")
        self.pd = pd
        self.dimensions = [0] * (pd.n + 1)
        self.resolutions: list[Resolution] = []
        self.by_degree: list[list[int]] = [[] for _ in range(pd.n + 1)]
        if limits.states is not None and pd.n >= limits.states.bit_length():
            raise ResourceLimit(f"2^{pd.n} resolutions exceed state limit {limits.states}")
        state_count = 1 << pd.n
        if limits.states is not None and state_count > limits.states:
            raise ResourceLimit("Resolution state limit exceeded")
        total = 0
        for state in range(state_count):
            degree = state.bit_count()
            r = smoothing(pd, state, base_edge, self.dimensions[degree])
            total += r.dimension
            if limits.generators is not None and total > limits.generators:
                raise ResourceLimit(f"Chain generators exceed limit {limits.generators}")
            self.dimensions[degree] += r.dimension
            self.resolutions.append(r)
            self.by_degree[degree].append(state)
        # Conservative logical bit estimate; not a promise about Python RSS.
        self.logical_matrix_bits = sum(a * b for a, b in
                                       zip(self.dimensions, self.dimensions[1:]))
        if limits.matrix_bits is not None and self.logical_matrix_bits > limits.matrix_bits:
            raise ResourceLimit(f"Logical matrix bits {self.logical_matrix_bits} exceed "
                                f"limit {limits.matrix_bits}")
        self.saddles: dict[int, tuple[Saddle, ...]] = {}
        for state, source in enumerate(self.resolutions):
            self.saddles[state] = tuple(
                make_saddle(source, self.resolutions[state | (1 << crossing)],
                            state | (1 << crossing))
                for crossing in range(pd.n) if not (state >> crossing & 1))

    def columns(self, degree: int) -> Iterator[int]:
        for state in self.by_degree[degree]:
            source = self.resolutions[state]
            for code in range(source.dimension):
                labels = source.decode(code)
                column = 0
                for saddle in self.saddles[state]:
                    target = self.resolutions[saddle.target_state]
                    for out in saddle.images(labels, target):
                        column ^= 1 << (target.offset + out)
                yield column

    def check_d_squared(self) -> bool:
        """An independent matrix-composition check, without a rank oracle."""
        previous: list[int] | None = None
        for degree in range(self.pd.n):
            current = list(self.columns(degree))
            if previous is not None:
                for column in previous:
                    result = 0
                    while column:
                        bit = column & -column
                        result ^= current[bit.bit_length() - 1]
                        column ^= bit
                    if result:
                        return False
            previous = current
        return True

    def homology(self, check_d2: bool = False) -> dict:
        if check_d2 and not self.check_d_squared():
            raise ArithmeticError("Differentials fail d^2 = 0")
        ranks = [rank_f2(self.columns(i)) for i in range(self.pd.n)]
        padded_ranks = [0] + ranks + [0]
        homology = [dim - padded_ranks[i] - padded_ranks[i + 1]
                    for i, dim in enumerate(self.dimensions)]
        if any(dim < 0 for dim in homology):
            raise ArithmeticError("Negative homology dimension")
        total_rank = sum(homology)
        if total_rank < 1:
            raise ArithmeticError("Reduced homology of a knot must be nonzero")
        return {"reduced_rank_f2": total_rank,
                "resolutions": len(self.resolutions),
                "chain_generators": sum(self.dimensions),
                "chain_dimensions": self.dimensions,
                "differential_ranks": ranks,
                "unshifted_homology_dimensions": homology,
                "logical_matrix_bits": self.logical_matrix_bits,
                "d_squared_checked": check_d2}


def fox_determinant(pd: PlanarDiagram) -> int:
    """Absolute Alexander evaluation at -1; value 1 does NOT imply unknot."""
    if pd.n == 0:
        return 1
    uf = UnionFind(2 * pd.n)
    for _, b, _, d in pd.crossings:
        uf.union(b, d)
    roots = sorted({uf.find(i) for i in range(2 * pd.n)})
    if len(roots) != pd.n:
        raise ArithmeticError("Unexpected number of Wirtinger arcs")
    index = {root: i for i, root in enumerate(roots)}
    matrix = [[0] * pd.n for _ in range(pd.n)]
    for i, (a, b, c, _) in enumerate(pd.crossings):
        matrix[i][index[uf.find(b)]] += 2
        matrix[i][index[uf.find(a)]] -= 1
        matrix[i][index[uf.find(c)]] -= 1
    return abs(determinant_bareiss([row[:-1] for row in matrix[:-1]]))


def recognize(pd: PlanarDiagram, limits: Limits = Limits(),
              check_d2: bool = False, determinant_filter: bool = True,
              basepoint_label: int | None = None) -> dict:
    """Exact on completion; ResourceLimit must never be interpreted as NO."""
    base_edge = pd.basepoint(basepoint_label)
    base = {"crossings": pd.n, "quasipolynomial_guarantee": False,
            "implementation": "exact-reference-not-Lackenby-hierarchy"}
    if not pd.n:
        return {**base, "status": "unknot", "is_unknot": True,
                "method": "crossing-free-circle", "reduced_rank_f2": 1}
    if determinant_filter:
        determinant = fox_determinant(pd)
        base["determinant"] = determinant
        if determinant != 1:
            return {**base, "status": "nontrivial", "is_unknot": False,
                    "method": "fox-determinant-obstruction"}
    result = CubeComplex(pd, base_edge, limits).homology(check_d2)
    trivial = result["reduced_rank_f2"] == 1
    return {**base, **result, "status": "unknot" if trivial else "nontrivial",
            "is_unknot": trivial, "method": "reduced-khovanov-F2"}
