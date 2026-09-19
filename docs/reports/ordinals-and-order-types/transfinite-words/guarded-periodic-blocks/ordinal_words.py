"""Exact symbolic subsequence calculations for finite-poset words below omega**2.

Omega tokens denote periodic infinite words, NOT finite truncations. Correctness
of the token abstraction is proved in article.tex. Only Python's standard library
is required. Alphabet elements are integers 0,...,n-1. Ideals use bit masks.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Iterable, Iterator, Sequence

Token = tuple[int, int]  # (0, letter) or (1, nonempty ideal mask)
Word = tuple[Token, ...]


def letter(a: int) -> Token:
    return (0, a)


def omega(ideal: int) -> Token:
    return (1, ideal)


@dataclass(frozen=True)
class Poset:
    """A finite poset, represented by the upper set of each element."""
    upper: tuple[int, ...]

    def __post_init__(self) -> None:
        n = len(self.upper)
        full = (1 << n) - 1
        for a, mask in enumerate(self.upper):
            if not 0 <= mask <= full or not (mask & (1 << a)):
                raise ValueError("Relation must be bounded and reflexive")
            for b in range(n):
                if mask & (1 << b):
                    if a != b and self.upper[b] & (1 << a):
                        raise ValueError("Relation must be antisymmetric")
                    if self.upper[b] & ~mask:
                        raise ValueError("Relation must be transitive")

    @property
    def n(self) -> int:
        return len(self.upper)

    @property
    def full(self) -> int:
        return (1 << self.n) - 1

    def le(self, a: int, b: int) -> bool:
        return bool(self.upper[a] & (1 << b))

    def is_ideal(self, mask: int) -> bool:
        return 0 <= mask <= self.full and all(
            not (self.upper[a] & mask) or mask & (1 << a)
            for a in range(self.n)
        )

    def ideals(self, nonempty: bool = False) -> tuple[int, ...]:
        values = (m for m in range(int(nonempty), self.full + 1)
                  if self.is_ideal(m))
        return tuple(sorted(values, key=lambda m: (m.bit_count(), m)))

    def maximal_elements(self, ideal: int) -> tuple[int, ...]:
        if not ideal or not self.is_ideal(ideal):
            raise ValueError("Expected a nonempty ideal")
        return tuple(a for a in range(self.n)
                     if ideal & (1 << a) and (self.upper[a] & ideal) == 1 << a)

    def validate_word(self, w: Word) -> None:
        for kind, value in w:
            if kind == 0:
                if not 0 <= value < self.n:
                    raise ValueError("Invalid letter")
            elif kind == 1:
                if not value or not self.is_ideal(value):
                    raise ValueError("Invalid recurrent ideal")
            else:
                raise ValueError("Unknown token kind")

    @classmethod
    def antichain(cls, n: int) -> Poset:
        if n < 0:
            raise ValueError("Negative alphabet size")
        return cls(tuple(1 << a for a in range(n)))

    @classmethod
    def chain(cls, n: int) -> Poset:
        if n < 0:
            raise ValueError("Negative alphabet size")
        return cls(tuple(((1 << n) - 1) ^ ((1 << a) - 1)
                         for a in range(n)))


def embeds(poset: Poset, source: Word, target: Word) -> bool:
    """Greedy exact decision; assumes validated words; O(len(source)+len(target)).

    A successful finite match in an omega token leaves a periodic tail available.
    A successful omega match consumes that entire target omega token cofinally.
    """
    j = 0
    for kind, value in source:
        while j < len(target):
            tkind, tvalue = target[j]
            if kind == 0:
                if tkind == 0:
                    j += 1
                    if poset.le(value, tvalue):
                        break
                elif tvalue & (1 << value):
                    break
                else:
                    j += 1
            else:
                j += 1
                if tkind == 1 and not (value & ~tvalue):
                    break
        else:
            return False
    return True


def embeds_dp(poset: Poset, source: Word, target: Word) -> bool:
    """Independent branching dynamic program on the exact token abstraction."""
    @lru_cache(maxsize=None)
    def solve(i: int, j: int) -> bool:
        if i == len(source):
            return True
        if j == len(target):
            return False
        sk, sv = source[i]
        tk, tv = target[j]
        if sk == 0 and tk == 0 and poset.le(sv, tv) and solve(i + 1, j + 1):
            return True
        if sk == 0 and tk == 1 and tv & (1 << sv) and solve(i + 1, j):
            return True
        if sk == 1 and tk == 1 and not (sv & ~tv) and solve(i + 1, j + 1):
            return True
        return solve(i, j + 1)
    return solve(0, 0)


def normalize(w: Word) -> Word:
    """Remove each finite suffix absorbed by the following omega token."""
    out: list[Token] = []
    for token in w:
        kind, value = token
        if kind == 1:
            while out and out[-1][0] == 0 and value & (1 << out[-1][1]):
                out.pop()
        out.append(token)
    return tuple(out)


def length_pair(w: Word) -> tuple[int, int]:
    """Return (r,k) representing the ordinal length omega*r+k."""
    r = k = 0
    for kind, _ in w:
        if kind == 1:
            r += 1
            k = 0
        else:
            k += 1
    return r, k


def tokens(poset: Poset, family: Iterable[int]) -> tuple[Token, ...]:
    return tuple(letter(a) for a in range(poset.n)) + tuple(omega(d) for d in family)


def words(alphabet: Sequence[Token], max_tokens: int) -> Iterator[Word]:
    if max_tokens < 0:
        raise ValueError("Negative word length bound")
    for k in range(max_tokens + 1):
        yield from product(alphabet, repeat=k)


def guard(poset: Poset, family: Sequence[int], new: int, u: Word) -> Word:
    """The two guard constructions from the product-embedding theorem."""
    if not new or not poset.is_ideal(new) or new in family:
        raise ValueError("New token must be a new nonempty ideal")
    if any(not (new & ~old) for old in family):
        raise ValueError("An old support contains the new support")
    if new != poset.full:
        a = next(a for a in range(poset.n) if not new & (1 << a))
        return u + (letter(a),)
    proper = next((r for r in family if r != poset.full), None)
    if proper is None:
        raise ValueError("Full support requires an earlier proper support")
    a = next(a for a in range(poset.n) if not proper & (1 << a))
    return u + (letter(a), omega(proper))


def encode_product(poset: Poset, family: Sequence[int], new: int,
                   components: Sequence[Word]) -> Word:
    if not components:
        raise ValueError("Product must have at least one component")
    out: list[Token] = []
    for i, u in enumerate(components):
        if i:
            out.append(omega(new))
        out.extend(guard(poset, family, new, u))
    return tuple(out)


def naturally_labelled_posets(n: int) -> tuple[Poset, ...]:
    """All distinct orders with a<b numerically whenever a<_P b.

    These are NOT all labelled posets. Every unlabelled n-point poset is
    represented, possibly more than once. Suitable here only for very small n.
    """
    if not 0 <= n <= 6:
        raise ValueError("Exhaustive generation supports 0 <= n <= 6")
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    seen: set[tuple[int, ...]] = set()
    for bits in range(1 << len(pairs)):
        upper = [1 << a for a in range(n)]
        for i, (a, b) in enumerate(pairs):
            if bits & (1 << i):
                upper[a] |= 1 << b
        for a in reversed(range(n)):
            for b in range(a + 1, n):
                if upper[a] & (1 << b):
                    upper[a] |= upper[b]
        seen.add(tuple(upper))
    return tuple(Poset(u) for u in sorted(seen))
