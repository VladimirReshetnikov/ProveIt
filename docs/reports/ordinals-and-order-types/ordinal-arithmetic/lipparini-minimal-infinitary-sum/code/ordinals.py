"""Exact finite Cantor-normal-form arithmetic for ordinals below epsilon_0.

No floating point, external packages, or limit truncations are used.  The
mathematical theorem concerns arbitrary ordinals; this engine only represents
finite hereditary Cantor normal forms, hence ordinals below epsilon_0.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
from typing import Iterable

@total_ordering
@dataclass(frozen=True, slots=True)
class Ordinal:
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self) -> None:
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError('An exponent must be an Ordinal')
            if not isinstance(coefficient, int) or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers')
            if previous is not None and not exponent < previous:
                raise ValueError('CNF exponents must be strictly decreasing')
            previous = exponent

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        return self.terms < other.terms

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __str__(self) -> str:
        if not self:
            return '0'
        pieces = []
        for exponent, coefficient in self.terms:
            if not exponent:
                pieces.append(str(coefficient))
                continue
            if exponent == ONE:
                power = 'w'
            elif exponent.is_finite:
                power = 'w^' + str(exponent)
            else:
                power = 'w^(' + str(exponent) + ')'
            pieces.append(power if coefficient == 1 else power + '*' + str(coefficient))
        return ' + '.join(pieces)

    @property
    def is_finite(self) -> bool:
        return not self or self.terms[0][0] == ZERO

    @property
    def is_successor(self) -> bool:
        return bool(self) and self.terms[-1][0] == ZERO

    @property
    def is_limit(self) -> bool:
        return bool(self) and not self.is_successor

    @property
    def finite_part(self) -> int:
        return self.terms[-1][1] if self.is_successor else 0

    def limit_part(self) -> 'Ordinal':
        return Ordinal(self.terms[:-1]) if self.is_successor else self

    def predecessor(self) -> 'Ordinal':
        if not self.is_successor:
            raise ValueError('Only a successor ordinal has a predecessor')
        return self.delete_last_monomial()

    def delete_last_monomial(self) -> 'Ordinal':
        if not self:
            raise ValueError('Cannot delete a monomial from zero')
        exponent, coefficient = self.terms[-1]
        last = ((exponent, coefficient - 1),) if coefficient > 1 else ()
        return Ordinal(self.terms[:-1] + last)

    def __add__(self, other: 'Ordinal') -> 'Ordinal':
        """Ordinary ordinal addition, not natural addition."""
        if not isinstance(other, Ordinal):
            return NotImplemented
        if not other:
            return self
        exponent, coefficient = other.terms[0]
        kept = []
        for exp, coeff in self.terms:
            if exp > exponent:
                kept.append((exp, coeff))
            elif exp == exponent:
                coefficient += coeff
                break
            else:
                break
        return Ordinal(tuple(kept) + ((exponent, coefficient),) + other.terms[1:])

    def natural_sum(self, other: 'Ordinal') -> 'Ordinal':
        terms = dict(self.terms)
        for exponent, coefficient in other.terms:
            terms[exponent] = terms.get(exponent, 0) + coefficient
        return Ordinal(tuple(sorted(terms.items(), reverse=True)))

    def natural_times_finite(self, n: int) -> 'Ordinal':
        if not isinstance(n, int) or n < 0:
            raise ValueError('The multiplier must be a nonnegative integer')
        return Ordinal(tuple((e, c * n) for e, c in self.terms)) if n else ZERO

    def natural_times_omega(self) -> 'Ordinal':
        return Ordinal(tuple((exponent + ONE, coefficient)
                             for exponent, coefficient in self.terms))

    def right_remainder(self, upper: 'Ordinal') -> 'Ordinal':
        """Return the unique d with self + d = upper; require self <= upper."""
        if self > upper:
            raise ValueError('The lower endpoint exceeds the upper endpoint')
        index = 0
        while index < min(len(self.terms), len(upper.terms)):
            ae, ac = self.terms[index]
            be, bc = upper.terms[index]
            if (ae, ac) == (be, bc):
                index += 1
                continue
            if ae < be:
                return Ordinal(upper.terms[index:])
            if ae == be and ac < bc:
                return Ordinal(((be, bc - ac),) + upper.terms[index + 1:])
            raise AssertionError('Comparison/remainder inconsistency')
        return Ordinal(upper.terms[index:])


def finite(n: int) -> Ordinal:
    if not isinstance(n, int) or n < 0:
        raise ValueError('A finite ordinal must be a nonnegative integer')
    return Ordinal(((Ordinal(), n),)) if n else Ordinal()

ZERO = Ordinal()
ONE = finite(1)
OMEGA = Ordinal(((ONE, 1),))


def omega_power(exponent: Ordinal, coefficient: int = 1) -> Ordinal:
    return Ordinal(((exponent, coefficient),))


def natural_sum(values: Iterable[Ordinal]) -> Ordinal:
    result = ZERO
    for value in values:
        result = result.natural_sum(value)
    return result


def chi(t: Ordinal) -> int:
    limit = t.limit_part()
    return int(bool(limit) and limit.terms[-1][0].is_successor)


def constant_value(t: Ordinal) -> Ordinal:
    return t.natural_times_omega().natural_sum(OMEGA if chi(t) else ZERO)


def base(e: Ordinal) -> Ordinal:
    if not e:
        raise ValueError('A tail cut is positive')
    if e.is_successor:
        return constant_value(e.predecessor())
    exponent = e.terms[-1][0]
    if exponent.is_successor:
        return e.natural_times_omega()
    return e.delete_last_monomial().natural_times_omega().natural_sum(omega_power(exponent))


def weight(e: Ordinal, a: Ordinal) -> Ordinal:
    if not e or a < e:
        raise ValueError('Require 0 < e <= a')
    if e.is_successor:
        return e.predecessor().right_remainder(a)
    if e.terms[-1][0].is_successor:
        return ONE + e.right_remainder(a)  # order is crucial: 1 + d, not d + 1
    return e.delete_last_monomial().right_remainder(a)


@dataclass(frozen=True)
class Profile:
    cut: Ordinal
    heads: tuple[Ordinal, ...] = ()

    def __post_init__(self) -> None:
        if not self.cut:
            raise ValueError('A tail cut must be positive')
        if any(a < self.cut for a in self.heads):
            raise ValueError('All exceptional heads must be at least the cut')
        object.__setattr__(self, 'heads', tuple(sorted(self.heads, reverse=True)))

    def le(self, other: 'Profile') -> bool:
        if self.cut > other.cut:
            return False
        relevant = tuple(a for a in self.heads if a >= other.cut)
        return len(relevant) <= len(other.heads) and all(
            a <= b for a, b in zip(relevant, other.heads))

    def value(self) -> Ordinal:
        return base(self.cut).natural_sum(natural_sum(weight(self.cut, a) for a in self.heads))

    def lipparini_S(self) -> Ordinal:
        e = self.cut
        if e.is_successor:
            z = e.predecessor()
            return z.natural_times_omega().natural_sum(
                natural_sum(z.right_remainder(a) for a in self.heads))
        if e.terms[-1][0].is_successor:
            return e.natural_times_omega().natural_sum(
                natural_sum(e.right_remainder(a) for a in self.heads))
        p = e.delete_last_monomial()
        return p.natural_times_omega().natural_sum(omega_power(e.terms[-1][0])).natural_sum(
            natural_sum(p.right_remainder(a) for a in self.heads))

    def __str__(self) -> str:
        return 'cut=' + str(self.cut) + '; heads=[' + ', '.join(map(str, self.heads)) + ']'
