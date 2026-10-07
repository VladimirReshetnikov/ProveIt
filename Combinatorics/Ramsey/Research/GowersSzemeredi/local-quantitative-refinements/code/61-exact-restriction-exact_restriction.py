#!/usr/bin/env python3
"""Exact certificates for torsion-uniform Freiman restriction.

Finite abelian groups are explicit products of cyclic groups. All character,
threshold, and coloring calculations use integers or fractions; no numerical
Fourier transforms are used. This is a small-instance reference implementation,
not a polynomial-time algorithm in a compressed presentation of a group.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import lcm, prod
from typing import Iterable, Mapping, Sequence

Point = tuple[int, ...]

@dataclass(frozen=True)
class AbelianGroup:
    moduli: tuple[int, ...]

    def __post_init__(self) -> None:
        if any(not isinstance(q, int) or q < 1 for q in self.moduli):
            raise ValueError("All cyclic moduli must be positive integers")

    @property
    def zero(self) -> Point:
        return (0,) * len(self.moduli)

    @property
    def order(self) -> int:
        return prod(self.moduli)

    @property
    def exponent(self) -> int:
        return lcm(*self.moduli) if self.moduli else 1

    def elements(self) -> tuple[Point, ...]:
        return tuple(product(*(range(q) for q in self.moduli)))

    def check(self, x: Point) -> None:
        if len(x) != len(self.moduli) or any(
                a < 0 or a >= q for a, q in zip(x, self.moduli)):
            raise ValueError(f"Invalid group element {x!r}")

    def add(self, x: Point, y: Point) -> Point:
        return tuple((a + b) % q for a, b, q in zip(x, y, self.moduli))

    def sub(self, x: Point, y: Point) -> Point:
        return tuple((a - b) % q for a, b, q in zip(x, y, self.moduli))

    def scale(self, k: int, x: Point) -> Point:
        return tuple((k * a) % q for a, q in zip(x, self.moduli))

    def char_numerator(self, chi: Point, x: Point) -> int:
        """chi(x) in R/Z, represented with denominator self.exponent."""
        den = self.exponent
        return sum(a * b * (den // q)
                   for a, b, q in zip(chi, x, self.moduli)) % den

    def char_small(self, chi: Point, x: Point) -> bool:
        v = self.char_numerator(chi, x)
        den = self.exponent
        return 5 * min(v, den - v) < den  # STRICT radius 1/5


def sumset(group: AbelianGroup, a: Iterable[Point], b: Iterable[Point],
           subtract: bool = False) -> set[Point]:
    aa, bb = tuple(a), tuple(b)
    op = group.sub if subtract else group.add
    return {op(x, y) for x in aa for y in bb}


def multiple_sumset(group: AbelianGroup, a: Iterable[Point], k: int) -> set[Point]:
    if k < 0:
        raise ValueError("k must be nonnegative")
    a = tuple(a)
    ans = {group.zero}
    for _ in range(k):
        ans = sumset(group, ans, a)
    return ans


def sum_distribution(group: AbelianGroup, a: Iterable[Point], k: int
                     ) -> Counter[Point]:
    if k < 0:
        raise ValueError("k must be nonnegative")
    a = tuple(a)
    dist = Counter({group.zero: 1})
    for _ in range(k):
        nxt: Counter[Point] = Counter()
        for x, count in dist.items():
            for y in a:
                nxt[group.add(x, y)] += count
        dist = nxt
    return dist


def energy(group: AbelianGroup, a: Iterable[Point], k: int = 2) -> int:
    return sum(v * v for v in sum_distribution(group, a, k).values())


def ceil_log2(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    return (n - 1).bit_length()


def separating_characters(group: AbelianGroup, forbidden: Iterable[Point]
                          ) -> list[Point]:
    """Greedy conditional-expectation version of the halving argument."""
    remaining = set(forbidden)
    for x in remaining:
        group.check(x)
    if group.zero in remaining:
        raise ValueError("The forbidden set must not contain zero")
    initial = len(remaining)
    chars: list[Point] = []
    allchars = group.elements()
    while remaining:
        chi = min(allchars, key=lambda c:
                  sum(group.char_small(c, x) for x in remaining))
        nxt = {x for x in remaining if group.char_small(chi, x)}
        assert 2 * len(nxt) <= len(remaining), "Halving lemma failed"
        chars.append(chi)
        remaining = nxt
    assert len(chars) <= ceil_log2(initial + 1)
    return chars


def color_points(group: AbelianGroup, points: Iterable[Point],
                 chars: Sequence[Point], m: int) -> dict[tuple[int, ...], set[Point]]:
    if m < 1:
        raise ValueError("m must be positive")
    cells: dict[tuple[int, ...], set[Point]] = defaultdict(set)
    for x in points:
        group.check(x)
        key = tuple((5 * m * group.char_numerator(c, x)) // group.exponent
                    for c in chars)
        cells[key].add(x)
    return dict(cells)


def avoidance_partition(group: AbelianGroup, forbidden: Iterable[Point], m: int
                        ) -> tuple[list[Point], list[set[Point]]]:
    forbidden = set(forbidden)
    chars = separating_characters(group, forbidden)
    cells = list(color_points(group, group.elements(), chars, m).values())
    assert len(cells) <= (5 * m) ** ceil_log2(len(forbidden) + 1)
    return chars, cells


def verify_avoidance(group: AbelianGroup, cells: Sequence[set[Point]],
                     forbidden: Iterable[Point], m: int) -> bool:
    forbidden = set(forbidden)
    for cell in cells:
        sums = multiple_sumset(group, cell, m)
        if sumset(group, sums, sums, subtract=True) & forbidden:
            return False
    return True


def graph_of(g: AbelianGroup, h: AbelianGroup,
             phi: Mapping[Point, Point]) -> tuple[AbelianGroup, set[Point]]:
    for x, y in phi.items():
        g.check(x)
        h.check(y)
    return AbelianGroup(g.moduli + h.moduli), {x + y for x, y in phi.items()}


def freiman_partition(g: AbelianGroup, h: AbelianGroup,
                      phi: Mapping[Point, Point], m: int
                      ) -> tuple[list[Point], list[set[Point]], set[Point]]:
    if not phi or m < 1:
        raise ValueError("Require a nonempty graph and positive order")
    ambient, graph = graph_of(g, h, phi)
    sums = multiple_sumset(ambient, graph, m)
    differences = sumset(ambient, sums, sums, subtract=True)
    cut = len(g.moduli)
    defects = {z[cut:] for z in differences if z[:cut] == g.zero}
    assert h.zero in defects
    chars = separating_characters(h, defects - {h.zero})
    cells: dict[tuple[int, ...], set[Point]] = defaultdict(set)
    for x, y in phi.items():
        key = tuple((5 * m * h.char_numerator(c, y)) // h.exponent for c in chars)
        cells[key].add(x)
    return chars, list(cells.values()), defects


def is_freiman(g: AbelianGroup, h: AbelianGroup,
               phi: Mapping[Point, Point], subset: Iterable[Point], m: int) -> bool:
    subset = set(subset)
    if not subset:
        return True
    ambient, graph = graph_of(g, h, {x: phi[x] for x in subset})
    sums = multiple_sumset(ambient, graph, m)
    values: dict[Point, Point] = {}
    cut = len(g.moduli)
    for z in sums:
        x, y = z[:cut], z[cut:]
        if x in values and values[x] != y:
            return False
        values[x] = y
    return True


def bsg_core(group: AbelianGroup, a: Iterable[Point]
             ) -> tuple[set[Point], dict[str, int | str]]:
    """Conservative c/8, 2^21 c^-9 BSG certificate from the article."""
    a = tuple(sorted(set(a)))
    n = len(a)
    if not n:
        raise ValueError("Require a nonempty set")
    counts = Counter(group.sub(x, y) for x in a for y in a)
    e2 = sum(z * z for z in counts.values())
    c = Fraction(e2, n ** 3)
    delta = c / 2
    popular = {d for d, count in counts.items() if count >= c * n / 2}
    neigh = [{j for j in range(n) if group.sub(a[i], a[j]) in popular}
             for i in range(n)]
    threshold = delta * delta * n / 32
    bad = {(i, j) for i in range(n) for j in range(n)
           if len(neigh[i] & neigh[j]) < threshold}
    best_score, best_u = None, None
    for v in range(n):
        u = {i for i in range(n) if v in neigh[i]}
        b = sum((i, j) in bad for i in u for j in u)
        score = len(u) - Fraction(16, 1) * b / (delta * n)
        if best_score is None or score > best_score:
            best_score, best_u = score, u
    assert best_score is not None and best_u is not None
    assert best_score >= delta * n / 2
    size_u = len(best_u)
    core_indices = {i for i in best_u
                    if 4 * sum((i, j) in bad for j in best_u) <= size_u}
    core = {a[i] for i in core_indices}
    diff = sumset(group, core, core, subtract=True)
    assert len(core) >= c * n / 8
    assert len(diff) <= 2 ** 21 * c ** -9 * n
    return core, {"input_size": n, "energy2": e2, "c": str(c),
                  "core_size": len(core), "difference_size": len(diff)}
