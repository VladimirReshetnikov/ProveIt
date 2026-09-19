"""Exact finite Cantor normal forms below epsilon_0 (Python standard library).

The mathematics in the article applies to all ordinals. This implementation
only represents hereditary finite Cantor normal forms, hence ordinals < epsilon_0.
No routine attempts to infer an infinite sequence's threshold from samples.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering
from typing import Iterable

@total_ordering
@dataclass(frozen=True)
class Ord:
    terms: tuple[tuple['Ord', int], ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.terms, tuple):
            raise TypeError('terms must be a tuple')
        previous = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ord):
                raise TypeError('exponents must be Ord objects')
            if not isinstance(coefficient, int) or isinstance(coefficient, bool) or coefficient <= 0:
                raise ValueError('coefficients must be positive integers')
            if previous is not None and not exponent < previous:
                raise ValueError('exponents must be strictly decreasing')
            previous = exponent

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ord):
            return NotImplemented
        return self.terms < other.terms

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __add__(self, other: 'Ord') -> 'Ord':
        """Ordinary ordinal addition, not natural addition."""
        if not isinstance(other, Ord):
            return NotImplemented
        if not other:
            return self
        leading, coefficient = other.terms[0]
        kept = [(e, c) for e, c in self.terms if e > leading]
        existing = next((c for e, c in self.terms if e == leading), 0)
        return Ord(tuple(kept + [(leading, existing + coefficient)] + list(other.terms[1:])))

    def natural(self, other: 'Ord') -> 'Ord':
        coefficients = dict(self.terms)
        for e, c in other.terms:
            coefficients[e] = coefficients.get(e, 0) + c
        return Ord(tuple(sorted(coefficients.items(), reverse=True)))

    def times_omega_natural(self) -> 'Ord':
        return Ord(tuple((e + ONE, c) for e, c in self.terms))

    def split_finite(self) -> tuple['Ord', int]:
        if self.terms and not self.terms[-1][0]:
            return Ord(self.terms[:-1]), self.terms[-1][1]
        return self, 0

    @property
    def is_successor(self) -> bool:
        return self.split_finite()[1] > 0

    def predecessor(self) -> 'Ord':
        infinite, n = self.split_finite()
        if n == 0:
            raise ValueError('zero and limit ordinals have no predecessor')
        return infinite + finite(n - 1)

    def as_finite(self) -> int:
        infinite, n = self.split_finite()
        if infinite:
            raise ValueError('ordinal is not finite')
        return n

    def remove_last_monomial(self) -> 'Ord':
        if not self:
            raise ValueError('zero has no last monomial')
        e, c = self.terms[-1]
        return Ord(self.terms[:-1] + (((e, c - 1),) if c > 1 else ()))

    def __str__(self) -> str:
        if not self:
            return '0'
        pieces = []
        for e, c in self.terms:
            if not e:
                pieces.append(str(c))
            else:
                monomial = 'w' if e == ONE else f'w^({e})'
                pieces.append(monomial if c == 1 else f'{monomial}*{c}')
        return ' + '.join(pieces)


def finite(n: int) -> Ord:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError('a finite ordinal requires a nonnegative integer')
    return Ord(((Ord(), n),)) if n else Ord()

ZERO = Ord()
ONE = finite(1)
OMEGA = Ord(((ONE, 1),))


def omega_power(exponent: Ord, coefficient: int = 1) -> Ord:
    return Ord(((exponent, coefficient),))


def natural_sum(values: Iterable[Ord]) -> Ord:
    out = ZERO
    for value in values:
        out = out.natural(value)
    return out


def difference(base: Ord, target: Ord) -> Ord:
    """Unique delta with base + delta == target, requiring base <= target."""
    if target < base:
        raise ValueError('target must be at least base')
    if target == base:
        return ZERO
    i = 0
    while i < len(base.terms) and i < len(target.terms) and base.terms[i] == target.terms[i]:
        i += 1
    if i == len(base.terms):
        result = Ord(target.terms[i:])
    else:
        a_exp, a_coef = target.terms[i]
        b_exp, b_coef = base.terms[i]
        if a_exp > b_exp:
            result = Ord(target.terms[i:])
        elif a_exp == b_exp and a_coef > b_coef:
            result = Ord(((a_exp, a_coef - b_coef),) + target.terms[i + 1:])
        else:
            raise AssertionError('comparison and difference disagree')
    assert base + result == target
    return result


def successor_exponent_block(value: Ord) -> bool:
    """Does the least positive CNF exponent exist and have a predecessor?"""
    infinite, _ = value.split_finite()
    return bool(infinite) and infinite.terms[-1][0].is_successor


def evaluate_s(epsilon: Ord, entries: Iterable[Ord] = ()) -> Ord:
    """Lipparini S, with a certified threshold and finite prefix/exception list.

    entries may contain subthreshold entries; they are ignored. Multiplicities
    matter. The unlisted infinite background must actually have this epsilon.
    """
    if not epsilon:
        raise ValueError('the threshold of an omega-sequence must be positive')
    special = [a for a in entries if a >= epsilon]
    if epsilon.is_successor:
        b = epsilon.predecessor()
        return b.times_omega_natural().natural(natural_sum(difference(b, a) for a in special))
    rho = epsilon.terms[-1][0]
    if rho.is_successor:
        return epsilon.times_omega_natural().natural(natural_sum(difference(epsilon, a) for a in special))
    hat = epsilon.remove_last_monomial()
    return natural_sum([hat.times_omega_natural(), omega_power(rho)] +
                       [difference(hat, a) for a in special])


def evaluate_n(epsilon: Ord, entries: Iterable[Ord] = ()) -> Ord:
    """The proposed explicit N formula, independent of evaluate_s."""
    if not epsilon:
        raise ValueError('the threshold of an omega-sequence must be positive')
    special = [a for a in entries if a >= epsilon]
    if epsilon.is_successor:
        b = epsilon.predecessor()
        correction = OMEGA if successor_exponent_block(b) else ZERO
        return natural_sum([b.times_omega_natural(), correction] +
                           [difference(b, a) for a in special])
    rho = epsilon.terms[-1][0]
    if rho.is_successor:
        return epsilon.times_omega_natural().natural(
            natural_sum(ONE + difference(epsilon, a) for a in special))
    hat = epsilon.remove_last_monomial()
    return natural_sum([hat.times_omega_natural(), omega_power(rho)] +
                       [difference(hat, a) for a in special])


def evaluate_n_via_correction(epsilon: Ord, entries: Iterable[Ord] = ()) -> Ord:
    """Separate S-plus-correction implementation for cross-checking."""
    data = tuple(entries)
    s = evaluate_s(epsilon, data)
    if epsilon.is_successor:
        return s.natural(OMEGA) if successor_exponent_block(epsilon.predecessor()) else s
    if epsilon.terms[-1][0].is_successor:
        k = sum(epsilon <= a < epsilon + OMEGA for a in data)
        return s + finite(k)
    return s


def evaluate_block(lam: Ord, n: int, entries: Iterable[Ord]) -> Ord:
    """Independent block-normal-form formula; lam must be corrected limit."""
    if not lam or lam.is_successor or not successor_exponent_block(lam):
        raise ValueError('lam must be a positive limit with successor final exponent')
    if not isinstance(n, int) or n < 0:
        raise ValueError('n must be nonnegative')
    data = tuple(entries)
    far = [difference(lam, a) for a in data if a >= lam + OMEGA]
    c = sum(difference(lam, a).as_finite() - n + 1
            for a in data if lam + finite(n) <= a < lam + OMEGA)
    return natural_sum([lam.times_omega_natural(), omega_power(ONE, n) if n else ZERO,
                        finite(c)] + far)
