"""Exact hereditary Cantor normal forms below epsilon_0, standard library only.

JSON: a nonnegative integer, or [[exponent, positive_coefficient], ...]
in strictly decreasing exponent order. Exponents use the same syntax.
No floating point arithmetic or finite replacement for omega is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
from typing import Any, Iterable


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self) -> None:
        for i, (exponent, coefficient) in enumerate(self.terms):
            if not isinstance(exponent, Ordinal):
                raise TypeError('An exponent must be an Ordinal')
            if type(coefficient) is not int or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers')
            if i and not self.terms[i - 1][0] > exponent:
                raise ValueError('CNF exponents must be strictly decreasing')

    @staticmethod
    def finite(n: int) -> 'Ordinal':
        if type(n) is not int or n < 0:
            raise ValueError('A finite ordinal must be a nonnegative integer')
        return Ordinal() if n == 0 else Ordinal(((Ordinal(), n),))

    @staticmethod
    def omega_power(exponent: 'Ordinal') -> 'Ordinal':
        return Ordinal(((exponent, 1),))

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __lt__(self, other: 'Ordinal') -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        return self.terms < other.terms

    def __add__(self, other: 'Ordinal') -> 'Ordinal':
        """Ordinary (noncommutative) ordinal addition."""
        if not isinstance(other, Ordinal):
            return NotImplemented
        if not other:
            return self
        lead, coefficient = other.terms[0]
        prefix = [(e, c) for e, c in self.terms if e > lead]
        matching = next((c for e, c in self.terms if e == lead), 0)
        return Ordinal(tuple(prefix + [(lead, matching + coefficient)]
                             + list(other.terms[1:])))

    def natural_sum(self, other: 'Ordinal') -> 'Ordinal':
        coefficients = dict(self.terms)
        for e, c in other.terms:
            coefficients[e] = coefficients.get(e, 0) + c
        return Ordinal(tuple(sorted(coefficients.items(), reverse=True)))

    @property
    def is_pure(self) -> bool:
        return len(self.terms) == 1 and self.terms[0][1] == 1

    def to_json(self) -> Any:
        if not self:
            return 0
        if len(self.terms) == 1 and not self.terms[0][0]:
            return self.terms[0][1]
        return [[e.to_json(), c] for e, c in self.terms]

    @staticmethod
    def from_json(value: Any, depth: int = 0) -> 'Ordinal':
        if depth > 100:
            raise ValueError('Ordinal nesting exceeds the safety limit 100')
        if type(value) is int:
            return Ordinal.finite(value)
        if not isinstance(value, list):
            raise ValueError('An ordinal must be an integer or a CNF list')
        terms = []
        for term in value:
            if not isinstance(term, list) or len(term) != 2:
                raise ValueError('Each CNF term must be [exponent, coefficient]')
            terms.append((Ordinal.from_json(term[0], depth + 1), term[1]))
        return Ordinal(tuple(terms))

    def __str__(self) -> str:
        if not self:
            return '0'
        result = []
        for e, c in self.terms:
            if not e:
                result.append(str(c))
            else:
                power = 'omega' if e == ONE else f'omega^({e})'
                result.append(power if c == 1 else f'{power}*{c}')
        return ' + '.join(result)


ZERO = Ordinal()
ONE = Ordinal.finite(1)
OMEGA = Ordinal.omega_power(ONE)


def ordinal_sum(values: Iterable[Ordinal]) -> Ordinal:
    answer = ZERO
    for x in values:
        answer = answer + x
    return answer


def natural_sum(values: Iterable[Ordinal]) -> Ordinal:
    answer = ZERO
    for x in values:
        answer = answer.natural_sum(x)
    return answer


def product_height(factors: list[Ordinal]) -> Ordinal:
    """Classical Milner--Rado/product-height formula, a separate benchmark.

    Empty product has height 1; a zero factor makes the product empty.
    This is not the ideal-DAG algorithm used by heights.py.
    """
    if not factors:
        return ONE
    if any(not x for x in factors):
        return ZERO
    rho = max(x.terms[-1][0] for x in factors)
    bases = []
    for x in factors:
        terms = []
        for e, c in x.terms:
            if e < rho:
                continue
            if e == rho and x.terms[-1][0] == rho:
                c -= 1
            if c:
                terms.append((e, c))
        bases.append(Ordinal(tuple(terms)))
    return natural_sum(bases) + Ordinal.omega_power(rho)
