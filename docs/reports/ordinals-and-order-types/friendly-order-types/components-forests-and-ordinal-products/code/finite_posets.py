"""Exact, independent finite-poset computations for friendly order type.

Python 3.10+; standard library only. Elements are 0,...,n-1. up[x] is the
inclusive principal upper set of x, encoded as a bit mask. The direct
rank algorithm does NOT use the component formula proved in the article.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property, lru_cache
from itertools import combinations
from typing import Iterable, Iterator


def bits(mask: int) -> Iterator[int]:
    """Yield the set bit indices, in increasing order."""
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class FinitePoset:
    up: tuple[int, ...]

    def __post_init__(self) -> None:
        n = len(self.up)
        whole = (1 << n) - 1
        for x, ux in enumerate(self.up):
            if not isinstance(ux, int) or ux < 0 or ux & ~whole:
                raise ValueError("An upper-set mask has out-of-range bits")
            if not (ux >> x) & 1:
                raise ValueError("The relation is not reflexive")
            for y in bits(ux):
                if x != y and (self.up[y] >> x) & 1:
                    raise ValueError("The relation is not antisymmetric")
                if self.up[y] & ~ux:
                    raise ValueError("The relation is not transitive")

    @property
    def n(self) -> int:
        return len(self.up)

    @property
    def whole(self) -> int:
        return (1 << self.n) - 1

    @cached_property
    def down(self) -> tuple[int, ...]:
        return tuple(sum(1 << x for x in range(self.n)
                         if (self.up[x] >> y) & 1) for y in range(self.n))

    @cached_property
    def inc(self) -> tuple[int, ...]:
        return tuple(self.whole & ~(self.up[x] | self.down[x])
                     for x in range(self.n))

    @classmethod
    def from_relations(cls, n: int, relations: Iterable[tuple[int, int]]) -> FinitePoset:
        """Take a transitive closure. Cycles are rejected by validation."""
        if n < 0:
            raise ValueError("The cardinality must be nonnegative")
        up = [1 << i for i in range(n)]
        for x, y in relations:
            if not (0 <= x < n and 0 <= y < n):
                raise ValueError("An element is outside range(n)")
            up[x] |= 1 << y
        for k in range(n):
            for x in range(n):
                if (up[x] >> k) & 1:
                    up[x] |= up[k]
        return cls(tuple(up))

    @classmethod
    def chain(cls, n: int) -> FinitePoset:
        return cls.from_relations(n, ((i, i + 1) for i in range(n - 1)))

    @classmethod
    def antichain(cls, n: int) -> FinitePoset:
        return cls.from_relations(n, ())

    def components(self, mask: int | None = None) -> list[int]:
        """Incomparability components of the induced subposet on mask."""
        mask = self.whole if mask is None else mask
        if mask < 0 or mask & ~self.whole:
            raise ValueError("Invalid induced-subposet mask")
        remaining = mask
        result = []
        while remaining:
            seen = 0
            todo = remaining & -remaining
            while todo:
                bit = todo & -todo
                todo ^= bit
                if bit & seen:
                    continue
                seen |= bit
                x = bit.bit_length() - 1
                todo |= self.inc[x] & mask & ~seen
            result.append(seen)
            remaining &= ~seen
        return result

    def component_formula(self) -> int:
        return self.n - len(self.components())

    def exact_rank(self) -> tuple[int, list[dict[str, int]], int]:
        """Direct residual-tree DP, an optimal sequence, and states visited."""
        @lru_cache(maxsize=None)
        def rank(mask: int) -> int:
            best = 0
            for x in bits(mask):
                if self.inc[x] & mask:
                    best = max(best, 1 + rank(mask & ~self.up[x]))
            return best

        value = rank(self.whole)
        mask = self.whole
        certificate = []
        while rank(mask):
            for x in bits(mask):
                friends = self.inc[x] & mask
                after = mask & ~self.up[x]
                if friends and rank(mask) == rank(after) + 1:
                    y = next(bits(friends))
                    certificate.append({"selected": x, "friend": y,
                                        "before": mask, "after": after})
                    mask = after
                    break
            else:
                raise AssertionError("DP reconstruction failed")
        self.check_certificate(certificate)
        return value, certificate, rank.cache_info().currsize

    def check_certificate(self, certificate: list[dict[str, int]]) -> int:
        mask = self.whole
        for step in certificate:
            x, y = step["selected"], step["friend"]
            if not (0 <= x < self.n and 0 <= y < self.n):
                raise ValueError("Invalid certificate vertex")
            if step["before"] != mask or not ((mask >> x) & 1):
                raise ValueError("Selected vertex is absent or residual is wrong")
            if not (self.inc[x] & mask & (1 << y)):
                raise ValueError("Witness is not an available incomparable friend")
            mask &= ~self.up[x]
            if step["after"] != mask:
                raise ValueError("Wrong residual after a move")
        return mask

    def constructive_certificate(self) -> list[dict[str, int]]:
        """The proof's maximal non-cut-vertex strategy, not the rank DP."""
        components = self.components()
        # The components are totally ordered. Count points below a representative.
        components.sort(key=lambda c: self.down[next(bits(c))].bit_count(),
                        reverse=True)
        mask = self.whole
        result = []
        for original in components:
            active = original
            while active.bit_count() > 1:
                for x in bits(active):
                    if self.up[x] & active != 1 << x:
                        continue
                    rest = active & ~(1 << x)
                    if len(self.components(rest)) == 1:
                        y = next(bits(self.inc[x] & active))
                        after = mask & ~self.up[x]
                        result.append({"selected": x, "friend": y,
                                       "before": mask, "after": after})
                        mask, active = after, rest
                        break
                else:
                    raise AssertionError("Maximal non-cut-vertex lemma failed")
        self.check_certificate(result)
        return result

    def endpoints(self) -> tuple[bool, bool]:
        return (any(u == self.whole for u in self.up),
                any(d == self.whole for d in self.down))

    def height(self) -> int:
        @lru_cache(maxsize=None)
        def height_from(x: int) -> int:
            return 1 + max((height_from(y) for y in bits(self.up[x] & ~(1 << x))),
                           default=0)
        return max((height_from(x) for x in range(self.n)), default=0)

    def width(self) -> int:
        @lru_cache(maxsize=None)
        def clique(mask: int) -> int:
            if not mask:
                return 0
            x = next(bits(mask))
            return max(clique(mask & ~(1 << x)), 1 + clique(mask & self.inc[x]))
        return clique(self.whole)

    def invariants(self) -> tuple[int, int, int, int]:
        return self.n, self.height(), self.width(), self.exact_rank()[0]

    def covers(self) -> list[tuple[int, int]]:
        return [(x, y) for x in range(self.n)
                for y in bits(self.up[x] & ~(1 << x))
                if not (self.up[x] & self.down[y] & ~((1 << x) | (1 << y)))]

    def product(self, other: FinitePoset) -> FinitePoset:
        m = other.n
        return FinitePoset(tuple(
            sum(1 << (a * m + b) for a in bits(self.up[x]) for b in bits(other.up[y]))
            for x in range(self.n) for y in range(m)))


def naturally_labelled_posets(n: int) -> Iterator[FinitePoset]:
    """All partial orders compatible with 0<1<...<n-1 as a linear extension.

    No isomorphism quotient is taken. Every isomorphism class has a
    representative here. Exponential exhaustive enumeration; n<=6 recommended.
    """
    if n < 0:
        raise ValueError("The cardinality must be nonnegative")
    pairs = list(combinations(range(n), 2))
    for relation in range(1 << len(pairs)):
        up = [1 << x for x in range(n)]
        for k, (x, y) in enumerate(pairs):
            if (relation >> k) & 1:
                up[x] |= 1 << y
        if all(not ((up[x] >> y) & 1) or not (up[y] & ~up[x]) for x, y in pairs):
            yield FinitePoset(tuple(up))
