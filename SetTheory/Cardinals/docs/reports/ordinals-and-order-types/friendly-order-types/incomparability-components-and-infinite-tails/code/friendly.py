"""Finite friendly order types: an independent rank oracle and a graph algorithm.

Python 3.9+; standard library only.  Vertices are 0, ..., n-1.  up[x] is the
bit mask of the *reflexive, transitive* principal upset of x.  The exact rank
routine implements the defining recurrence; it never calls the graph formula.
The graph formula and witness constructor never call the rank routine.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property, lru_cache
from typing import Iterable, Iterator, Optional, Sequence, Tuple


def vertices(mask: int) -> Iterator[int]:
    """Visit the set bits of a nonnegative integer in increasing order."""
    if mask < 0:
        raise ValueError("a vertex mask must be nonnegative")
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def size(mask: int) -> int:
    # Keep compatibility with Python 3.9, which does not have int.bit_count.
    return bin(mask).count("1")


@dataclass(frozen=True)
class FinitePoset:
    up: Tuple[int, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.up, tuple):
            raise TypeError("up must be an immutable tuple")
        full = (1 << len(self.up)) - 1
        for x, upset in enumerate(self.up):
            if not isinstance(upset, int) or upset < 0 or upset & ~full:
                raise ValueError("an upset contains an invalid vertex")
            if not upset & (1 << x):
                raise ValueError("the relation is not reflexive")
            for y in vertices(upset & ~(1 << x)):
                if self.up[y] & (1 << x):
                    raise ValueError("the relation is not antisymmetric")
                if self.up[y] & ~upset:
                    raise ValueError("the relation is not transitive")

    @property
    def n(self) -> int:
        return len(self.up)

    @property
    def full(self) -> int:
        return (1 << self.n) - 1

    @cached_property
    def down(self) -> Tuple[int, ...]:
        result = [0] * self.n
        for x, upset in enumerate(self.up):
            for y in vertices(upset):
                result[y] |= 1 << x
        return tuple(result)

    @cached_property
    def incomparable(self) -> Tuple[int, ...]:
        return tuple(self.full & ~(self.up[x] | self.down[x])
                     for x in range(self.n))

    def _mask(self, mask: Optional[int]) -> int:
        if mask is None:
            return self.full
        if not isinstance(mask, int) or mask < 0 or mask & ~self.full:
            raise ValueError("invalid induced-subposet mask")
        return mask

    @classmethod
    def from_relations(cls, n: int,
                       relations: Iterable[Tuple[int, int]]) -> FinitePoset:
        """Take the reflexive transitive closure; reject nontrivial cycles."""
        if not isinstance(n, int) or n < 0:
            raise ValueError("n must be a nonnegative integer")
        up = [1 << x for x in range(n)]
        for x, y in relations:
            if not (0 <= x < n and 0 <= y < n):
                raise ValueError("relation endpoint out of range")
            up[x] |= 1 << y
        for k in range(n):
            for x in range(n):
                if up[x] & (1 << k):
                    up[x] |= up[k]
        return cls(tuple(up))

    @classmethod
    def chain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError("negative cardinality")
        full = (1 << n) - 1
        return cls(tuple(full & ~((1 << x) - 1) for x in range(n)))

    @classmethod
    def antichain(cls, n: int) -> FinitePoset:
        if n < 0:
            raise ValueError("negative cardinality")
        return cls(tuple(1 << x for x in range(n)))

    def disjoint_sum(self, other: FinitePoset) -> FinitePoset:
        return FinitePoset(self.up + tuple(u << self.n for u in other.up))

    def ordinal_sum(self, other: FinitePoset) -> FinitePoset:
        second = other.full << self.n
        return FinitePoset(tuple(u | second for u in self.up)
                           + tuple(u << self.n for u in other.up))

    def product(self, other: FinitePoset) -> FinitePoset:
        q = other.n
        up = []
        for x in range(self.n):
            for y in range(q):
                row = 0
                for xx in vertices(self.up[x]):
                    row |= other.up[y] << (xx * q)
                up.append(row)
        return FinitePoset(tuple(up))

    def components(self, mask: Optional[int] = None) -> Tuple[int, ...]:
        """Connected components of the induced incomparability graph."""
        unseen = self._mask(mask)
        answer = []
        while unseen:
            frontier = unseen & -unseen
            unseen ^= frontier
            component = frontier
            while frontier:
                bit = frontier & -frontier
                frontier ^= bit
                x = bit.bit_length() - 1
                new = self.incomparable[x] & unseen
                unseen ^= new
                frontier |= new
                component |= new
            answer.append(component)
        return tuple(answer)

    def ordered_components(self, mask: Optional[int] = None) -> Tuple[int, ...]:
        components = self.components(mask)
        representatives = [(c & -c).bit_length() - 1 for c in components]
        # Distinct components are totally ordered.  Count the earlier ones.
        order = sorted(range(len(components)), key=lambda j: sum(
            bool(self.up[representatives[i]] & (1 << representatives[j]))
            for i in range(len(components)) if i != j))
        return tuple(components[j] for j in order)

    def maxima(self, mask: Optional[int] = None) -> Tuple[int, ...]:
        active = self._mask(mask)
        return tuple(x for x in vertices(active)
                     if self.up[x] & active == 1 << x)

    def graph_rank(self, mask: Optional[int] = None) -> int:
        active = self._mask(mask)
        return size(active) - len(self.components(active))

    def exact_rank(self, mask: Optional[int] = None) -> int:
        """Exponential reference implementation of the defining tree rank."""
        active = self._mask(mask)
        up, inc = self.up, self.incomparable

        @lru_cache(maxsize=None)
        def rank(state: int) -> int:
            best = 0
            for x in vertices(state):
                if inc[x] & state:
                    best = max(best, 1 + rank(state & ~up[x]))
            return best

        return rank(active)

    def optimal_witness(self) -> Tuple[int, ...]:
        """Construct a friendly sequence of length n - components.

        Work in descending component order.  Inside a component, delete a
        maximal non-articulation vertex until just one vertex remains.  A later
        move in a lower component may remove those higher singleton leftovers.
        """
        sequence = []
        for component in reversed(self.ordered_components()):
            remaining = component
            while size(remaining) > 1:
                for x in self.maxima(remaining):
                    smaller = remaining & ~(1 << x)
                    if len(self.components(smaller)) == 1:
                        sequence.append(x)
                        remaining = smaller
                        break
                else:
                    raise AssertionError("maximal non-cut-vertex lemma failed")
        result = tuple(sequence)
        if not self.is_friendly(result):
            raise AssertionError("the constructed witness is not friendly")
        return result

    def is_friendly(self, sequence: Sequence[int]) -> bool:
        remaining = self.full
        for x in sequence:
            if not isinstance(x, int) or not 0 <= x < self.n:
                return False
            if not remaining & (1 << x):
                return False
            if not self.incomparable[x] & remaining:
                return False
            remaining &= ~self.up[x]
        return True


def naturally_labeled_posets(n: int) -> Iterator[FinitePoset]:
    """Enumerate exactly the posets with x <_P y implying x < y.

    Extend a poset by a new largest *label*.  The predecessors of the new
    vertex may be any downset of the old poset.  This yields every natural
    labeling exactly once, not every arbitrary labeling or every isomorphism
    class exactly once.  Every finite isomorphism class does occur.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if n == 0:
        yield FinitePoset(())
        return
    bit = 1 << (n - 1)
    for old in naturally_labeled_posets(n - 1):
        for ideal in range(1 << old.n):
            if any(old.down[x] & ~ideal for x in vertices(ideal)):
                continue
            yield FinitePoset(tuple(u | bit if ideal & (1 << x) else u
                                    for x, u in enumerate(old.up)) + (bit,))
