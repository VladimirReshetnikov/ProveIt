"""Finite hereditary Cantor-normal-form trees for ordinals below epsilon_0.

The code provides comparison, natural addition and multiplication, ordinary
ordinal addition, and omega exponentiation. It is not Kleene's O and does
not recognize arbitrary program-generated well-orders.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self):
        if not isinstance(self.terms, tuple):
            raise TypeError('CNF terms must be a tuple')
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError('Each exponent must be an Ordinal')
            if not isinstance(coefficient, int) or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers')
            if previous is not None and not previous > exponent:
                raise ValueError('CNF exponents must be strictly decreasing')
            previous = exponent

    @classmethod
    def natural(cls, n: int):
        if not isinstance(n, int) or n < 0:
            raise ValueError('Natural ordinal requires a nonnegative integer')
        return cls() if n == 0 else cls(((cls(), n),))

    def __lt__(self, other):
        if not isinstance(other, Ordinal):
            return NotImplemented
        for (a, m), (b, n) in zip(self.terms, other.terms):
            if a != b:
                return a < b
            if m != n:
                return m < n
        return len(self.terms) < len(other.terms)

    def omega_power(self):
        return Ordinal(((self, 1),))

    def natural_add(self, other: 'Ordinal'):
        if not isinstance(other, Ordinal):
            raise TypeError('Expected Ordinal')
        result = dict(self.terms)
        for exponent, coefficient in other.terms:
            result[exponent] = result.get(exponent, 0)+coefficient
        return Ordinal(tuple(sorted(result.items(), reverse=True)))

    def natural_mul(self, other: 'Ordinal'):
        if not isinstance(other, Ordinal):
            raise TypeError('Expected Ordinal')
        result = {}
        for a, m in self.terms:
            for b, n in other.terms:
                exponent = a.natural_add(b)
                result[exponent] = result.get(exponent, 0)+m*n
        return Ordinal(tuple(sorted(result.items(), reverse=True)))

    def ordinal_add(self, other: 'Ordinal'):
        if not isinstance(other, Ordinal):
            raise TypeError('Expected Ordinal')
        if not other.terms:
            return self
        exponent, coefficient = other.terms[0]
        result = [(a, m) for a, m in self.terms if a > exponent]
        equal_coefficient = next((m for a, m in self.terms if a == exponent), 0)
        result.append((exponent, equal_coefficient+coefficient))
        result.extend(other.terms[1:])
        return Ordinal(tuple(result))

    def __str__(self):
        if not self.terms:
            return '0'
        pieces = []
        zero, one = Ordinal(), Ordinal.natural(1)
        for exponent, coefficient in self.terms:
            if exponent == zero:
                pieces.append(str(coefficient))
                continue
            base = 'omega' if exponent == one else f'omega^({exponent})'
            pieces.append(base if coefficient == 1 else f'{base}*{coefficient}')
        return ' + '.join(pieces)
