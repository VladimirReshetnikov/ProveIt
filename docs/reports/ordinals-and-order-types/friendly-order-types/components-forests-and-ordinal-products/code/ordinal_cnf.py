"""Hereditary Cantor normal forms for ordinals strictly below epsilon_0.

Pure exact symbolic arithmetic, Python 3.10+, standard library only.
The mathematical theorem in the article is NOT restricted to this notation
system. In particular, this module cannot encode omega_1 or epsilon_0.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import total_ordering
from typing import Iterable


@total_ordering
@dataclass(frozen=True)
class Ord:
    terms: tuple[tuple[Ord, int], ...] = ()

    def __post_init__(self) -> None:
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ord) or not isinstance(coefficient, int):
                raise TypeError("Use Ord exponents and integer coefficients")
            if coefficient <= 0:
                raise ValueError("CNF coefficients must be positive")
            if previous is not None and not exponent < previous:
                raise ValueError("CNF exponents must strictly decrease")
            previous = exponent

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __lt__(self, other: Ord) -> bool:
        if not isinstance(other, Ord):
            return NotImplemented
        for (a, c), (b, d) in zip(self.terms, other.terms):
            if a != b:
                return a < b
            if c != d:
                return c < d
        return len(self.terms) < len(other.terms)

    @staticmethod
    def nat(n: int) -> Ord:
        if not isinstance(n, int) or n < 0:
            raise ValueError("A finite ordinal must be a nonnegative integer")
        return Ord() if n == 0 else Ord(((Ord(), n),))

    @staticmethod
    def omega_power(exponent: Ord) -> Ord:
        return Ord(((exponent, 1),))

    def add(self, other: Ord) -> Ord:
        """Ordinary (noncommutative) ordinal addition."""
        if not other:
            return self
        lead, coefficient = other.terms[0]
        larger = [(e, c) for e, c in self.terms if e > lead]
        matching = next((c for e, c in self.terms if e == lead), 0)
        return Ord(tuple(larger + [(lead, matching + coefficient)]
                         + list(other.terms[1:])))

    def natural_sum(self, other: Ord) -> Ord:
        terms = dict(self.terms)
        for e, c in other.terms:
            terms[e] = terms.get(e, 0) + c
        return Ord(tuple(sorted(terms.items(), reverse=True)))

    def natural_product(self, other: Ord) -> Ord:
        terms: dict[Ord, int] = {}
        for e, c in self.terms:
            for f, d in other.terms:
                exponent = e.natural_sum(f)
                terms[exponent] = terms.get(exponent, 0) + c * d
        return Ord(tuple(sorted(terms.items(), reverse=True)))

    @property
    def finite_tail(self) -> int:
        return self.terms[-1][1] if self.terms and not self.terms[-1][0] else 0

    @property
    def is_finite(self) -> bool:
        return not self or (len(self.terms) == 1 and not self.terms[0][0])

    @property
    def is_successor(self) -> bool:
        return self.finite_tail > 0

    def predecessor(self) -> Ord:
        """Right predecessor, defined only for nonzero successor ordinals."""
        n = self.finite_tail
        if n == 0:
            raise ValueError("Zero and limit ordinals have no right predecessor")
        terms = self.terms[:-1]
        return Ord(terms + ((Ord(), n - 1),)) if n > 1 else Ord(terms)

    def to_json(self) -> list:
        return [[e.to_json(), c] for e, c in self.terms]

    def __str__(self) -> str:
        if not self:
            return "0"
        out = []
        for e, c in self.terms:
            if not e:
                out.append(str(c))
                continue
            base = "omega" if e == ONE else f"omega^({e})"
            out.append(base if c == 1 else f"{base}*{c}")
        return " + ".join(out)


ZERO, ONE = Ord(), Ord.nat(1)
OMEGA = Ord.omega_power(ONE)


def natural_product(factors: Iterable[Ord]) -> Ord:
    value = ONE
    for x in factors:
        value = value.natural_product(x)
    return value


def ordinal_box_friendly(factors: Iterable[Ord]) -> Ord:
    """Use the proved classification, not a transfinite rank computation."""
    factors = list(factors)
    if any(not x for x in factors):
        return ZERO
    nontrivial = [x for x in factors if x != ONE]
    if len(nontrivial) <= 1:
        return ZERO
    total = natural_product(nontrivial)
    if all(x.is_finite for x in nontrivial):
        return Ord.nat(total.finite_tail - 3)
    if all(x.is_successor for x in nontrivial):
        return total.predecessor()
    return total


def mixed_product_friendly(alphas: Iterable[Ord], cardinality: int,
                           has_greatest: bool) -> Ord:
    """Formula for infinite ordinal factors and a nonempty finite poset."""
    alphas = list(alphas)
    if not alphas or any(a.is_finite for a in alphas):
        raise ValueError("Supply at least one infinite ordinal")
    if cardinality < 1:
        raise ValueError("The finite poset must be nonempty")
    if cardinality == 1 and not has_greatest:
        raise ValueError("A singleton necessarily has a greatest element")
    if len(alphas) == 1 and cardinality == 1:
        return ZERO
    total = natural_product([*alphas, Ord.nat(cardinality)])
    return (total.predecessor() if has_greatest and
            all(a.is_successor for a in alphas) else total)
