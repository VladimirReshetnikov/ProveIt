"""Complete, exponential-time reduced Khovanov homology over F_2.

No Jones-polynomial-only decision, no floating point, no external CAS,
no unimplemented topology calls. The grading shown is the UNNORMALIZED
cube grading. Only total rank is used for unknot recognition.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterator
from .diagram import Diagram, DSU


class ResourceLimit(RuntimeError):
    """A user-selected resource limit was reached; no knot verdict follows."""


@dataclass(frozen=True)
class Resolution:
    circles: tuple[tuple[int, ...], ...]
    edge_circle: tuple[int, ...]

    @property
    def k(self) -> int:
        return len(self.circles)


def resolution(diagram: Diagram, state: int) -> Resolution:
    """0-smoothing: (a,b),(c,d); 1-smoothing: (a,d),(b,c)."""
    n = diagram.crossings
    if not 0 <= state < 1 << n:
        raise ValueError("Resolution state out of range")
    if n == 0:
        return Resolution(((0,),), (0,))
    dsu = DSU(2 * n)
    for i, (a, b, c, d) in enumerate(diagram.pd):
        pairs = ((a, d), (b, c)) if (state >> i) & 1 else ((a, b), (c, d))
        for x, y in pairs:
            dsu.union(x - 1, y - 1)
    groups: dict[int, list[int]] = defaultdict(list)
    for e in range(2 * n):
        groups[dsu.find(e)].append(e)
    circles = tuple(sorted((tuple(v) for v in groups.values()), key=lambda v: v[0]))
    edge_circle = [0] * (2 * n)
    for i, circle in enumerate(circles):
        for e in circle:
            edge_circle[e] = i
    # Circle 0 contains the marked arc 1; in the reduced complex it is labelled x.
    return Resolution(circles, tuple(edge_circle))


@dataclass(frozen=True)
class Saddle:
    target_state: int
    kind: str
    common: tuple[tuple[int, int], ...]
    changed_source: tuple[int, ...]
    changed_target: tuple[int, ...]

    def images(self, labels: int) -> tuple[int, ...]:
        """Bit 0 denotes label 1, bit 1 denotes label x in F_2[x]/(x^2)."""
        unchanged = 0
        for i, j in self.common:
            unchanged |= ((labels >> i) & 1) << j
        if self.kind == 'merge':
            i, j = self.changed_source
            a, b = (labels >> i) & 1, (labels >> j) & 1
            if a and b:
                return ()  # x*x=0
            return (unchanged | ((a | b) << self.changed_target[0]),)
        i = self.changed_source[0]
        a, b = self.changed_target
        if (labels >> i) & 1:
            return (unchanged | (1 << a) | (1 << b),)  # Delta(x)=x tensor x
        # Delta(1)=1 tensor x + x tensor 1
        return (unchanged | (1 << a), unchanged | (1 << b))


def make_saddle(source: Resolution, target: Resolution, state: int) -> Saddle:
    images = [set() for _ in source.circles]
    preimages = [set() for _ in target.circles]
    for a, b in zip(source.edge_circle, target.edge_circle):
        images[a].add(b)
        preimages[b].add(a)
    if target.k == source.k - 1:
        changed = [i for i, pre in enumerate(preimages) if len(pre) == 2]
        if len(changed) != 1 or any(len(im) != 1 for im in images):
            raise AssertionError("Invalid merge saddle")
        j = changed[0]
        pair = tuple(sorted(preimages[j]))
        common = tuple((i, next(iter(im))) for i, im in enumerate(images) if i not in pair)
        return Saddle(state, 'merge', common, pair, (j,))
    if target.k == source.k + 1:
        changed = [i for i, im in enumerate(images) if len(im) == 2]
        if len(changed) != 1 or any(len(pre) != 1 for pre in preimages):
            raise AssertionError("Invalid split saddle")
        i = changed[0]
        pair = tuple(sorted(images[i]))
        common = tuple((a, next(iter(im))) for a, im in enumerate(images) if a != i)
        return Saddle(state, 'split', common, (i,), pair)
    raise AssertionError("Saddle did not change circle count by one; check planarity")


@dataclass
class HomologyResult:
    total_rank: int
    generators: int
    cube_states: int
    blocks: list[dict[str, int]]
    differential_ranks: list[dict[str, int]]
    d_squared_checked: bool
    elimination_xors: int

    @property
    def is_unknot(self) -> bool:
        return self.total_rank == 1

    def as_json(self) -> dict:
        return {
            'coefficient_field': 'F_2',
            'variant': 'reduced; marked-circle subcomplex labelled x',
            'grading': 'unnormalized (h=popcount(state), q=h+k-2*popcount(labels))',
            'total_rank': self.total_rank,
            'generators': self.generators,
            'cube_states': self.cube_states,
            'homology_blocks': self.blocks,
            'differential_ranks': self.differential_ranks,
            'd_squared_checked': self.d_squared_checked,
            'elimination_xors': self.elimination_xors,
        }


class KhovanovComplex:
    """Construct the actual finite cochain complex, with optional resource guards.

    No guard is set by default. With a guard, exceeding it raises ResourceLimit,
    never a 'knotted' or 'unknot' answer. This class is not quasi-polynomial.
    """
    def __init__(self, diagram: Diagram, max_generators: int | None = None,
                 max_states: int | None = None):
        for name, limit in [('max_generators', max_generators), ('max_states', max_states)]:
            if limit is not None and (type(limit) is not int or limit < 1):
                raise ValueError(f'{name} must be a positive integer or None')
        self.diagram = diagram
        n = diagram.crossings
        if max_states is not None and (1 << n) > max_states:
            raise ResourceLimit(f'Need {1 << n} cube states; max_states={max_states}')
        self.resolutions: list[Resolution] = []
        self.bases: dict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
        self.row_indices: dict[tuple[int, int], dict[tuple[int, int], int]] = {}
        total = 0
        for state in range(1 << n):
            res = resolution(diagram, state)
            self.resolutions.append(res)
            size = 1 << (res.k - 1)
            total += size
            if max_generators is not None and total > max_generators:
                raise ResourceLimit(f'Reduced complex exceeds {max_generators} generators')
            h = state.bit_count()
            for free_labels in range(size):
                labels = (free_labels << 1) | 1
                q = h + res.k - 2 * labels.bit_count()
                self.bases[h, q].append((state, labels))
        self.generators = total
        for key, basis in self.bases.items():
            self.row_indices[key] = {generator: i for i, generator in enumerate(basis)}
        self.saddles: list[list[Saddle]] = []
        for state, source in enumerate(self.resolutions):
            outgoing = []
            for i in range(n):
                if not (state >> i) & 1:
                    target_state = state | (1 << i)
                    outgoing.append(make_saddle(source, self.resolutions[target_state],
                                                target_state))
            self.saddles.append(outgoing)

    def differential(self, state: int, labels: int) -> Iterator[tuple[int, int]]:
        for saddle in self.saddles[state]:
            for image in saddle.images(labels):
                if not image & 1:
                    raise AssertionError('Differential left the reduced subcomplex')
                yield (saddle.target_state, image)

    def check_d_squared(self) -> None:
        """Independently compose adjacent differential columns on every generator."""
        for basis in self.bases.values():
            for state, labels in basis:
                parity: set[tuple[int, int]] = set()
                for state1, labels1 in self.differential(state, labels):
                    for term in self.differential(state1, labels1):
                        if term in parity:
                            parity.remove(term)
                        else:
                            parity.add(term)
                if parity:
                    raise AssertionError(f'd^2 != 0 at {(state, labels)}: {parity}')

    def homology(self, check_d_squared: bool = False) -> HomologyResult:
        if check_d_squared:
            self.check_d_squared()
        ranks, xor_count = {}, 0
        for (h, q), basis in sorted(self.bases.items()):
            target = self.row_indices.get((h + 1, q), {})
            pivots: dict[int, int] = {}
            for state, labels in basis:
                column = 0
                for term in self.differential(state, labels):
                    if term not in target:
                        raise AssertionError(f'Differential has wrong grading: {term}')
                    column ^= 1 << target[term]
                while column:
                    pivot = column.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = column
                        break
                    column ^= pivots[pivot]
                    xor_count += 1
            ranks[h, q] = len(pivots)
        total_rank, blocks = 0, []
        for (h, q), basis in sorted(self.bases.items()):
            dimension = len(basis) - ranks.get((h - 1, q), 0) - ranks.get((h, q), 0)
            if dimension < 0:
                raise AssertionError('Negative homology dimension')
            if dimension:
                blocks.append({'h': h, 'q': q, 'rank': dimension})
                total_rank += dimension
        if total_rank != self.generators - 2 * sum(ranks.values()):
            raise AssertionError('Total-rank consistency check failed')
        return HomologyResult(total_rank, self.generators, len(self.resolutions), blocks,
                              [{'h': h, 'q': q, 'rank': r}
                               for (h, q), r in sorted(ranks.items()) if r],
                              check_d_squared, xor_count)


def reduced_khovanov(diagram: Diagram, *, check_d_squared: bool = False,
                      max_generators: int | None = None,
                      max_states: int | None = None) -> HomologyResult:
    return KhovanovComplex(diagram, max_generators, max_states).homology(check_d_squared)
