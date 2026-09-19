#!/usr/bin/env python3
"""Finite friendly order type: exact rank, graph formula, and witnesses.

Python 3.10+; standard library only. Labels are integers 0,...,n-1.
A poset is represented by reflexive principal upsets as integer bit masks.
The exact rank routine does NOT call the component formula.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from functools import cmp_to_key, lru_cache
from itertools import product as tuples
from typing import Iterator, Sequence


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Poset:
    up: tuple[int, ...]
    down: tuple[int, ...] = field(init=False, repr=False)
    inc: tuple[int, ...] = field(init=False, repr=False)

    def __post_init__(self) -> None:
        n = len(self.up)
        full = (1 << n) - 1
        for x, upper in enumerate(self.up):
            if upper < 0 or upper & ~full or not upper & (1 << x):
                raise ValueError("Upsets must be in-range reflexive bit masks")
            for y in bits(upper & ~(1 << x)):
                if self.up[y] & (1 << x):
                    raise ValueError("Relation is not antisymmetric")
                if self.up[y] & ~upper:
                    raise ValueError("Relation is not transitive")
        down = tuple(sum(1 << y for y in range(n) if self.up[y] & (1 << x))
                     for x in range(n))
        object.__setattr__(self, "down", down)
        object.__setattr__(self, "inc", tuple(full & ~(self.up[x] | down[x])
                                            for x in range(n)))

    @property
    def n(self) -> int:
        return len(self.up)

    @property
    def full(self) -> int:
        return (1 << self.n) - 1

    @property
    def has_least(self) -> bool:
        return bool(self.n) and any(m == self.full for m in self.up)

    @property
    def has_greatest(self) -> bool:
        common = self.full
        for m in self.up:
            common &= m
        return bool(common)

    def components(self) -> list[int]:
        """Incomparability components, each encoded as a vertex mask."""
        todo, result = self.full, []
        while todo:
            queue = todo & -todo
            todo ^= queue
            component = queue
            while queue:
                bit = queue & -queue
                queue ^= bit
                new = self.inc[bit.bit_length() - 1] & todo
                todo ^= new
                queue |= new
                component |= new
            result.append(component)
        return result

    def friendly_formula(self) -> int:
        return self.n - len(self.components())

    def exact_friendly_rank(self) -> int:
        """Exponential reference algorithm from the residual definition."""
        @lru_cache(maxsize=None)
        def rank(mask: int) -> int:
            answer = 0
            for x in bits(mask):
                if self.inc[x] & mask:
                    answer = max(answer, 1 + rank(mask & ~self.up[x]))
            return answer
        return rank(self.full)

    def incidence_rank_f2(self) -> int:
        """Independent Gaussian elimination on edge columns over F_2."""
        pivots: dict[int, int] = {}
        for x in range(self.n):
            for y in bits(self.inc[x] & ~((1 << (x + 1)) - 1)):
                v = (1 << x) | (1 << y)
                while v:
                    k = v.bit_length() - 1
                    if k in pivots:
                        v ^= pivots[k]
                    else:
                        pivots[k] = v
                        break
        return len(pivots)

    def optimal_witness(self) -> dict:
        """Construct selected vertices, surviving friends, and a forest.

        No exact rank evaluation is used. Each component is given a connected
        linear extension; all but its first point are read backwards.
        """
        components = self.components()

        def compare(c: int, d: int) -> int:
            x, y = next(bits(c)), next(bits(d))
            if self.up[x] & (1 << y):
                return -1
            if self.up[y] & (1 << x):
                return 1
            raise AssertionError("Distinct components must be comparable")

        components.sort(key=cmp_to_key(compare))
        extensions, parents = [], {}
        for component in components:
            remaining, prefix, extension = component, 0, []
            while remaining:
                candidates = [x for x in bits(remaining)
                              if self.down[x] & remaining == 1 << x
                              and (not prefix or self.inc[x] & prefix)]
                if not candidates:
                    raise AssertionError("Connected extension lemma failed")
                x = candidates[0]
                if prefix:
                    parents[x] = next(bits(self.inc[x] & prefix))
                extension.append(x)
                prefix |= 1 << x
                remaining &= ~(1 << x)
            extensions.append(extension)
        selected = [x for extension in reversed(extensions)
                    for x in reversed(extension[1:])]
        friends = [parents[x] for x in selected]
        witness = {"selected": selected, "friends": friends,
                   "omitted_roots": [extension[0] for extension in extensions],
                   "component_extensions": extensions,
                   "forest_edges": [[x, parents[x]] for x in selected]}
        self.verify_witness(witness)
        return witness

    def verify_witness(self, witness: dict) -> None:
        selected, friends = witness["selected"], witness["friends"]
        if len(selected) != len(friends):
            raise ValueError("Witness length mismatch")
        residual = self.full
        for x, y in zip(selected, friends):
            if not (0 <= x < self.n and 0 <= y < self.n):
                raise ValueError("Witness vertex out of range")
            if not residual & (1 << x):
                raise ValueError("Selected vertex is absent from residual")
            if not residual & self.inc[x] & (1 << y):
                raise ValueError("Friend is absent or comparable")
            residual &= ~self.up[x]
        if len(selected) != self.friendly_formula():
            raise ValueError("Witness is not of claimed optimal length")

    def relabel(self, permutation: Sequence[int]) -> Poset:
        if sorted(permutation) != list(range(self.n)):
            raise ValueError("Not a permutation")
        result = [0] * self.n
        for x in range(self.n):
            result[permutation[x]] = sum(1 << permutation[y] for y in bits(self.up[x]))
        return Poset(tuple(result))


def chain(n: int) -> Poset:
    if n < 0:
        raise ValueError("Size must be nonnegative")
    return Poset(tuple(((1 << n) - 1) & ~((1 << x) - 1) for x in range(n)))


def antichain(n: int) -> Poset:
    if n < 0:
        raise ValueError("Size must be nonnegative")
    return Poset(tuple(1 << x for x in range(n)))


def naturally_labelled_posets(n: int) -> Iterator[Poset]:
    """All relations satisfying x<_{P}y => x<y as integer labels.

    Not an isomorph-free enumeration. Every isomorphism type is represented.
    The predecessor set of the new, largest label is any order ideal.
    """
    if n < 0:
        raise ValueError("Size must be nonnegative")
    if n == 0:
        yield Poset(())
        return
    for p in naturally_labelled_posets(n - 1):
        for ideal in range(1 << (n - 1)):
            if all(not upper & ideal or ideal & (1 << x)
                   for x, upper in enumerate(p.up)):
                yield Poset(tuple(upper | ((1 << (n - 1)) if ideal & (1 << x) else 0)
                                  for x, upper in enumerate(p.up)) + (1 << (n - 1),))


def substitute(index: Poset, fibers: Sequence[Poset]) -> Poset:
    if len(fibers) != index.n or any(p.n == 0 for p in fibers):
        raise ValueError("One nonempty fiber is required per index point")
    offsets, offset = [], 0
    for p in fibers:
        offsets.append(offset)
        offset += p.n
    up = []
    for i, p in enumerate(fibers):
        other = sum(fibers[j].full << offsets[j]
                    for j in bits(index.up[i] & ~(1 << i)))
        up.extend((upper << offsets[i]) | other for upper in p.up)
    return Poset(tuple(up))


def substitution_formula(index: Poset, fibers: Sequence[Poset]) -> int:
    if len(fibers) != index.n or any(p.n == 0 for p in fibers):
        raise ValueError("One nonempty fiber is required per index point")
    answer = 0
    for component in index.components():
        vertices = list(bits(component))
        if len(vertices) == 1:
            answer += fibers[vertices[0]].friendly_formula()
        else:
            answer += sum(fibers[i].n for i in vertices) - 1
    return answer


def cartesian(a: Poset, b: Poset) -> Poset:
    return Poset(tuple(sum(b.up[j] << (k * b.n) for k in bits(a.up[i]))
                       for i in range(a.n) for j in range(b.n)))


def cartesian_formula(a: Poset, b: Poset) -> int:
    if not a.n or not b.n:
        return 0
    if a.n == 1:
        return b.friendly_formula()
    if b.n == 1:
        return a.friendly_formula()
    return (a.n * b.n - 1 - int(a.has_least and b.has_least)
            - int(a.has_greatest and b.has_greatest))


def ordinal_sum(*posets: Poset) -> Poset:
    nonempty = [p for p in posets if p.n]
    return substitute(chain(len(nonempty)), nonempty)


def disjoint_sum(*posets: Poset) -> Poset:
    nonempty = [p for p in posets if p.n]
    return substitute(antichain(len(nonempty)), nonempty)
