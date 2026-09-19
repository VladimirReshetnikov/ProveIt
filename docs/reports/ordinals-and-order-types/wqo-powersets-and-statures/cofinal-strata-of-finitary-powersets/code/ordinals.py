"""Exact hereditary Cantor normal forms below epsilon_0.

No floating point is used.  The paper's theorems allow arbitrary ordinal
exponents; this executable notation system deliberately stops below epsilon_0.
Ordinary addition is ``a + b``; Hessenberg operations are named explicitly.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
from typing import Iterable, Union


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self) -> None:
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError('Exponents must be Ordinal objects.')
            if type(coefficient) is not int or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers.')
            if previous is not None and not previous > exponent:
                raise ValueError('CNF exponents must be strictly decreasing.')
            previous = exponent

    @staticmethod
    def finite(n: int) -> 'Ordinal':
        if type(n) is not int or n < 0:
            raise ValueError('A finite ordinal must be a nonnegative integer.')
        return Ordinal(()) if n == 0 else Ordinal(((Ordinal(), n),))

    @staticmethod
    def coerce(x: Union['Ordinal', int]) -> 'Ordinal':
        return x if isinstance(x, Ordinal) else Ordinal.finite(x)

    @staticmethod
    def omega_power(exponent: Union['Ordinal', int]) -> 'Ordinal':
        return Ordinal(((Ordinal.coerce(exponent), 1),))

    @staticmethod
    def cnf(terms: Iterable[tuple[Union['Ordinal', int], int]]) -> 'Ordinal':
        merged: dict[Ordinal, int] = {}
        for exponent, coefficient in terms:
            exponent = Ordinal.coerce(exponent)
            if type(coefficient) is not int or coefficient < 0:
                raise ValueError('Coefficients must be nonnegative integers.')
            if coefficient:
                merged[exponent] = merged.get(exponent, 0) + coefficient
        return Ordinal(tuple(sorted(merged.items(), reverse=True)))

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        return self.terms < other.terms

    def __add__(self, other: Union['Ordinal', int]) -> 'Ordinal':
        """Ordinary ordinal addition, NOT natural addition."""
        other = Ordinal.coerce(other)
        if not other:
            return self
        lead, coefficient = other.terms[0]
        prefix = [(e, c) for e, c in self.terms if e > lead]
        matching = next((c for e, c in self.terms if e == lead), 0)
        return Ordinal(tuple(prefix + [(lead, matching + coefficient)]
                             + list(other.terms[1:])))

    def __radd__(self, other: Union['Ordinal', int]) -> 'Ordinal':
        return Ordinal.coerce(other) + self

    def times_finite(self, n: int) -> 'Ordinal':
        """Ordinary right multiplication by a finite ordinal."""
        if type(n) is not int or n < 0:
            raise ValueError('Multiplier must be a nonnegative integer.')
        if not n or not self:
            return Ordinal()
        exponent, coefficient = self.terms[0]
        return Ordinal(((exponent, coefficient * n),) + self.terms[1:])

    def natural_sum(self, other: Union['Ordinal', int]) -> 'Ordinal':
        other = Ordinal.coerce(other)
        return Ordinal.cnf(self.terms + other.terms)

    def natural_product(self, other: Union['Ordinal', int]) -> 'Ordinal':
        other = Ordinal.coerce(other)
        return Ordinal.cnf((e.natural_sum(f), c * d)
                           for e, c in self.terms for f, d in other.terms)

    def truncate(self, threshold: Union['Ordinal', int]) -> 'Ordinal':
        threshold = Ordinal.coerce(threshold)
        return Ordinal(tuple((e, c) for e, c in self.terms if e >= threshold))

    @property
    def degree(self) -> 'Ordinal':
        if not self:
            raise ValueError('The zero ordinal has no leading exponent.')
        return self.terms[0][0]

    def to_json(self):
        if not self:
            return 0
        if len(self.terms) == 1 and not self.terms[0][0]:
            return self.terms[0][1]
        return [[e.to_json(), c] for e, c in self.terms]

    @staticmethod
    def from_json(value) -> 'Ordinal':
        if type(value) is int:
            return Ordinal.finite(value)
        if not isinstance(value, list):
            raise ValueError('Use an integer or a list of [exponent, coefficient].')
        terms = []
        for pair in value:
            if not isinstance(pair, list) or len(pair) != 2:
                raise ValueError('Each CNF term must be [exponent, coefficient].')
            terms.append((Ordinal.from_json(pair[0]), pair[1]))
        # Validate the supplied canonical order rather than silently repairing it.
        return Ordinal(tuple(terms))

    def __str__(self) -> str:
        if not self:
            return '0'
        pieces = []
        for exponent, coefficient in self.terms:
            if not exponent:
                pieces.append(str(coefficient))
                continue
            if exponent == ONE:
                base = 'omega'
            elif len(exponent.terms) == 1 and not exponent.terms[0][0]:
                base = 'omega^' + str(exponent)
            else:
                base = 'omega^(' + str(exponent) + ')'
            pieces.append(base if coefficient == 1 else base + '*' + str(coefficient))
        return ' + '.join(pieces)


ZERO = Ordinal()
ONE = Ordinal.finite(1)
OMEGA = Ordinal.omega_power(1)


def natural_sum(values: Iterable[Ordinal]) -> Ordinal:
    result = ZERO
    for value in values:
        result = result.natural_sum(value)
    return result
