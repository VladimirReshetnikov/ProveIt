"""Exact support enumeration and a matroid down-up sampler.

All graph vertices are labelled: X=range(m), Y=range(n). A row is a bitmask
of its Y-neighbours. Perfectly matchable vertex sets are counted ONCE,
not with the multiplicity of their perfect matchings. Standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb, ceil, log
import random
from typing import Iterable, Sequence


def bits(mask: int) -> Iterable[int]:
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


@dataclass(frozen=True)
class BipartiteGraph:
    rows: tuple[int, ...]
    n: int

    def __post_init__(self) -> None:
        if self.n < 0 or any(a < 0 or a >> self.n for a in self.rows):
            raise ValueError("Neighbour bitmasks must fit the nonnegative shore size.")

    @property
    def m(self) -> int:
        return len(self.rows)

    def transpose(self) -> 'BipartiteGraph':
        return BipartiteGraph(tuple(sum(1 << i for i, row in enumerate(self.rows)
                                        if row >> j & 1) for j in range(self.n)), self.m)

    def active_core(self) -> 'BipartiteGraph':
        active_y = list(bits(self.y_neighbours((1 << self.m) - 1)))
        return BipartiteGraph(tuple(sum(1 << k for k, j in enumerate(active_y)
                                            if row >> j & 1)
                                     for row in self.rows if row), len(active_y))

    def y_neighbours(self, xmask: int) -> int:
        result = 0
        for i in bits(xmask):
            result |= self.rows[i]
        return result

    def matching(self, xmask: int | None = None,
                 ymask: int | None = None) -> dict[int, int]:
        """Maximum matching x -> y, by augmenting paths; no numerical algebra."""
        if xmask is None:
            xmask = (1 << self.m) - 1
        if ymask is None:
            ymask = (1 << self.n) - 1
        owner: dict[int, int] = {}

        def augment(x: int, seen: set[int]) -> bool:
            for y in bits(self.rows[x] & ymask):
                if y in seen:
                    continue
                seen.add(y)
                if y not in owner or augment(owner[y], seen):
                    owner[y] = x
                    return True
            return False

        for x in bits(xmask):
            augment(x, set())
        return {x: y for y, x in owner.items()}

    def matchable(self, xmask: int, ymask: int) -> bool:
        return (xmask.bit_count() == ymask.bit_count()
                and len(self.matching(xmask, ymask)) == xmask.bit_count())

    def supports(self) -> set[tuple[int, int]]:
        """Enumerate all partial matchings, merging equal covered-vertex sets."""
        states = {(0, 0)}
        for i, row in enumerate(self.rows):
            new = set(states)
            for a, b in states:
                for j in bits(row & ~b):
                    new.add((a | (1 << i), b | (1 << j)))
            states = new
        return states

    def coefficients(self, wx: Sequence[Fraction | int] | None = None,
                     wy: Sequence[Fraction | int] | None = None) -> list[Fraction]:
        wx = tuple(Fraction(x) for x in (wx if wx is not None else [1] * self.m))
        wy = tuple(Fraction(y) for y in (wy if wy is not None else [1] * self.n))
        if len(wx) != self.m or len(wy) != self.n or min(wx + wy, default=1) <= 0:
            raise ValueError("Provide positive weights of the correct lengths.")
        out = [Fraction(0)] * (min(self.m, self.n) + 1)
        for a, b in self.supports():
            weight = Fraction(1)
            for i in bits(a):
                weight *= wx[i]
            for j in bits(b):
                weight *= wy[j]
            out[a.bit_count()] += weight
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return out

    def is_independent(self, elements: Iterable[int]) -> bool:
        """Independence oracle for [I_m | A_H], ground elements 0..m+n-1.

        Private X-elements reserve their own slots. The selected Y-elements
        must be matched into the remaining X-slots.
        """
        ss = frozenset(elements)
        if any(e < 0 or e >= self.m + self.n for e in ss):
            raise ValueError("Ground element out of range.")
        reserved = sum(1 << e for e in ss if e < self.m)
        ys = sum(1 << (e - self.m) for e in ss if e >= self.m)
        available = ((1 << self.m) - 1) ^ reserved
        return len(self.matching(available, ys)) == ys.bit_count()

    def is_basis(self, elements: Iterable[int]) -> bool:
        ss = frozenset(elements)
        return len(ss) == self.m and self.is_independent(ss)

    def palindromic_core_test(self) -> bool:
        """Polynomial-time structural test; does not enumerate coefficients."""
        g = self.active_core()
        if g.m != g.n:
            return False
        if g.m == 0:
            return True
        matching = g.matching()
        if len(matching) != g.m:
            return False
        rel = tuple(sum(1 << j for j in range(g.m)
                        if g.rows[i] >> matching[j] & 1) for i in range(g.m))
        return all(rel[j] & ~rel[i] == 0 for i, row in enumerate(rel) for j in bits(row))

    def leaf_extension(self, ell: int) -> 'BipartiteGraph':
        if ell < 0:
            raise ValueError("Leaf multiplicity must be nonnegative.")
        rows = list(self.rows)
        for i in range(self.m):
            for a in range(ell):
                rows[i] |= 1 << (self.n + i * ell + a)
        for j in range(self.n):
            rows.extend([1 << j] * ell)
        return BipartiteGraph(tuple(rows), self.n + self.m * ell)


def polynomial_value(coefficients: Sequence[Fraction | int], t: Fraction | int) -> Fraction:
    result = Fraction(0)
    for a in reversed(coefficients):
        result = result * t + a
    return result


def ulc(coefficients: Sequence[Fraction | int], order: int) -> bool:
    if len(coefficients) > order + 1:
        return False
    c = list(coefficients) + [0] * (order + 1 - len(coefficients))
    positive = [k for k, a in enumerate(c) if a > 0]
    if positive and positive != list(range(min(positive), max(positive) + 1)):
        return False
    return all(c[k] ** 2 * comb(order, k - 1) * comb(order, k + 1)
               >= c[k - 1] * c[k + 1] * comb(order, k) ** 2
               for k in range(1, order))


def down_up_sample(graph: BipartiteGraph, steps: int, seed: int = 1,
                   weights: Sequence[Fraction | int] | None = None,
                   initial: Iterable[int] | None = None) -> tuple[int, int]:
    """Return one approximate support sample after exactly `steps` transitions.

    `weights` are MATROID element activities, in X-then-Y order, not occupied
    vertex activities. For occupied weights a_i,b_j and fugacity z, use
    weights=(1/a_i for i in X) + (z*b_j for j in Y). Exact rational choices.
    The default initial basis X represents the empty support.
    """
    if steps < 0:
        raise ValueError("steps must be nonnegative")
    r, N = graph.m, graph.m + graph.n
    lam = tuple(Fraction(w) for w in (weights if weights is not None else [1] * N))
    if len(lam) != N or min(lam, default=1) <= 0:
        raise ValueError("Activities must be positive and have one entry per vertex.")
    base = set(range(r) if initial is None else initial)
    if not graph.is_basis(base):
        raise ValueError("initial must be a basis")
    rng = random.Random(seed)
    if r == 0:
        return 0, 0
    for _ in range(steps):
        removed = rng.choice(sorted(base))
        rest = base - {removed}
        candidates = [e for e in range(N) if e not in rest and graph.is_basis(rest | {e})]
        # lcm denominator gives an exact integer-weighted random choice.
        from math import lcm
        denominator = lcm(*(lam[e].denominator for e in candidates))
        integer_weights = [int(lam[e] * denominator) for e in candidates]
        ticket = rng.randrange(sum(integer_weights))
        for e, w in zip(candidates, integer_weights):
            if ticket < w:
                base = rest | {e}
                break
            ticket -= w
    a = sum(1 << i for i in range(r) if i not in base)
    b = sum(1 << (e - r) for e in base if e >= r)
    assert graph.matchable(a, b)
    return a, b


def uniform_mixing_steps(m: int, n: int, epsilon: float) -> int:
    """Safe bound from t >= m log(binomial(m+n,m)/epsilon)."""
    if not 0 < epsilon < 1 or m < 0 or n < 0:
        raise ValueError("Invalid shore size or accuracy.")
    return 0 if m == 0 else ceil(m * (log(comb(m + n, m)) + log(1 / epsilon)))


if __name__ == '__main__':
    g = BipartiteGraph((14, 3, 5, 9), 4)
    print("Theta_3 coefficients:", [int(x) for x in g.coefficients()])
    print("Palindromic:", g.palindromic_core_test())
    steps = uniform_mixing_steps(g.m, g.n, 1e-6)
    print("Mixing bound:", steps, "steps; one sample:", down_up_sample(g, steps, 7))
