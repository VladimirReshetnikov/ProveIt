"""Exact hereditary Cantor normal forms below epsilon_0 (standard library only).

JSON: a natural number, or [[exponent, positive_coefficient], ...] with
strictly decreasing exponents; exponents have the same recursive format.
Only ordinal addition, natural sum, comparison and pure powers are needed.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
from typing import Any

@total_ordering
@dataclass(frozen=True)
class Ordinal:
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self) -> None:
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError('An exponent must be an Ordinal')
            if type(coefficient) is not int or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers')
            if previous is not None and not exponent < previous:
                raise ValueError('CNF exponents must strictly decrease')
            previous = exponent

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        return self.terms < other.terms

    def __bool__(self) -> bool:
        return bool(self.terms)

    @staticmethod
    def nat(n: int) -> 'Ordinal':
        if type(n) is not int or n < 0:
            raise ValueError('Expected a nonnegative integer')
        return Ordinal() if n == 0 else Ordinal(((Ordinal(), n),))

    @staticmethod
    def power(exponent: 'Ordinal') -> 'Ordinal':
        return Ordinal(((exponent, 1),))

    @staticmethod
    def parse(value: Any) -> 'Ordinal':
        if type(value) is int:
            return Ordinal.nat(value)
        if not isinstance(value, list):
            raise ValueError('An ordinal must be an integer or a CNF list')
        result = []
        for term in value:
            if not isinstance(term, list) or len(term) != 2:
                raise ValueError('A CNF term must be [exponent, coefficient]')
            result.append((Ordinal.parse(term[0]), term[1]))
        return Ordinal(tuple(result))

    def json(self) -> Any:
        if not self:
            return 0
        if len(self.terms) == 1 and not self.terms[0][0]:
            return self.terms[0][1]
        return [[e.json(), c] for e, c in self.terms]

    def __add__(self, other: 'Ordinal') -> 'Ordinal':
        """Ordinary, noncommutative ordinal addition."""
        if not isinstance(other, Ordinal):
            return NotImplemented
        if not other:
            return self
        e, c = other.terms[0]
        prefix = [(a, b) for a, b in self.terms if a > e]
        equal = next((b for a, b in self.terms if a == e), 0)
        return Ordinal(tuple(prefix + [(e, equal + c)] + list(other.terms[1:])))

    def natural_sum(self, other: 'Ordinal') -> 'Ordinal':
        coefficients = dict(self.terms)
        for e, c in other.terms:
            coefficients[e] = coefficients.get(e, 0) + c
        return Ordinal(tuple(sorted(coefficients.items(), reverse=True)))

    def right_times(self, n: int) -> 'Ordinal':
        """Ordinary multiplication by a finite ordinal on the right."""
        if type(n) is not int or n < 0:
            raise ValueError('Expected a nonnegative integer')
        result = ZERO
        # Binary powering for the associative operation of ordinal addition.
        base = self
        while n:
            if n & 1:
                result = result + base
            base = base + base
            n >>= 1
        return result

    def __str__(self) -> str:
        if not self:
            return '0'
        pieces = []
        for e, c in self.terms:
            if not e:
                pieces.append(str(c))
                continue
            if e == ONE:
                piece = 'omega'
            elif len(e.terms) == 1 and not e.terms[0][0]:
                piece = 'omega^' + str(e)
            else:
                piece = 'omega^(' + str(e) + ')'
            if c != 1:
                piece += '*' + str(c)
            pieces.append(piece)
        return ' + '.join(pieces)

ZERO = Ordinal()
ONE = Ordinal.nat(1)
OMEGA = Ordinal.power(ONE)
