"""Exact hereditary Cantor-normal-form arithmetic below epsilon_0.

This is a testing kernel, not a proof-assistant formalization.  It uses only the
Python standard library.  Finite test inputs cannot validate arbitrary limits.
All Ord instances are immutable and normalized; exponents are themselves Ord.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import total_ordering, lru_cache
from typing import Iterable, Sequence


@total_ordering
@dataclass(frozen=True, slots=True)
class Ord:
    terms: tuple[tuple['Ord', int], ...] = ()

    def __post_init__(self) -> None:
        last = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ord):
                raise TypeError('Every exponent must be an Ord.')
            if not isinstance(coefficient, int) or coefficient <= 0:
                raise ValueError('CNF coefficients must be positive integers.')
            if last is not None and not last > exponent:
                raise ValueError('CNF exponents must be strictly decreasing.')
            last = exponent

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __lt__(self, other: 'Ord') -> bool:
        if not isinstance(other, Ord):
            return NotImplemented
        return self.terms < other.terms

    @property
    def degree(self) -> 'Ord':
        if not self:
            raise ValueError('Zero has no degree in this implementation.')
        return self.terms[0][0]

    @property
    def tail(self) -> int:
        return self.terms[-1][1] if self and not self.terms[-1][0] else 0

    @property
    def support(self) -> tuple['Ord', ...]:
        return tuple(e for e, _ in self.terms)

    @property
    def leading(self) -> tuple['Ord', int]:
        if not self:
            raise ValueError('Zero has no leading monomial.')
        return self.terms[0]

    @property
    def positive_terms(self) -> int:
        return sum(bool(e) for e, _ in self.terms)

    def __str__(self) -> str:
        if not self:
            return '0'
        out = []
        for e, c in self.terms:
            if not e:
                out.append(str(c))
                continue
            base = 'w' if e == ONE else f'w^({e})'
            out.append(base if c == 1 else f'{base}*{c}')
        return ' + '.join(out)


ZERO = Ord()
ONE = Ord(((ZERO, 1),))


def finite(n: int) -> Ord:
    if not isinstance(n, int) or n < 0:
        raise ValueError('A finite ordinal must be a nonnegative integer.')
    return Ord(((ZERO, n),)) if n else ZERO


def mono(exponent: Ord, coefficient: int = 1) -> Ord:
    if coefficient < 0:
        raise ValueError('Negative coefficient.')
    return Ord(((exponent, coefficient),)) if coefficient else ZERO


OMEGA = mono(ONE)


def from_terms(terms: Iterable[tuple[Ord, int]]) -> Ord:
    """Natural sum of supplied monomial terms, with equal degrees collected."""
    result: dict[Ord, int] = {}
    for e, c in terms:
        if c < 0:
            raise ValueError('Negative coefficient.')
        if c:
            result[e] = result.get(e, 0) + c
    return Ord(tuple(sorted(result.items(), reverse=True)))


@lru_cache(maxsize=100000)
def add(a: Ord, b: Ord) -> Ord:
    """Ordinary ordinal addition."""
    if not b:
        return a
    e, c = b.terms[0]
    prefix = []
    for f, d in a.terms:
        if f > e:
            prefix.append((f, d))
        elif f == e:
            c += d
            break
        else:
            break
    return Ord(tuple(prefix) + ((e, c),) + b.terms[1:])


@lru_cache(maxsize=100000)
def natural_add(a: Ord, b: Ord) -> Ord:
    return from_terms(a.terms + b.terms)


def scale_all(a: Ord, n: int) -> Ord:
    """Natural product a tensor n for a finite n."""
    if n < 0:
        raise ValueError('Negative multiplier.')
    return Ord(tuple((e, c*n) for e, c in a.terms)) if n else ZERO


def scale_leading(a: Ord, n: int) -> Ord:
    """Ordinary right multiplication by a finite n."""
    if n < 0:
        raise ValueError('Negative multiplier.')
    if not a or not n:
        return ZERO
    e, c = a.leading
    return Ord(((e, c*n),) + a.terms[1:])


@lru_cache(maxsize=100000)
def mul(a: Ord, b: Ord) -> Ord:
    """Ordinary ordinal multiplication, with the right operand expanded."""
    if not a or not b:
        return ZERO
    pieces = []
    for e, c in b.terms:
        if e:
            pieces.append((add(a.degree, e), c))
        else:
            pieces.extend(scale_leading(a, c).terms)
    return Ord(tuple(pieces))


@lru_cache(maxsize=100000)
def natural_mul(a: Ord, b: Ord) -> Ord:
    return from_terms((natural_add(e, f), c*d)
                      for e, c in a.terms for f, d in b.terms)


@lru_cache(maxsize=100000)
def jacobsthal(a: Ord, b: Ord) -> Ord:
    """Jacobsthal's classical binary CNF formula (not the pivot formula)."""
    if not a or not b:
        return ZERO
    positive = tuple((add(a.degree, e), c) for e, c in b.terms if e)
    terminal = scale_all(a, b.tail)
    return Ord(positive + terminal.terms)


def fold(factors: Sequence[Ord], operation=jacobsthal) -> Ord:
    result = ONE
    for a in factors:
        result = operation(result, a)
    return result


def pivot_product(factors: Sequence[Ord]) -> Ord:
    """All-at-once cell formula: no calls to Jacobsthal multiplication."""
    if not factors:
        return ONE
    if any(not a for a in factors):
        return ZERO
    n = len(factors)
    later_tails = [1] * n
    for i in range(n-2, -1, -1):
        later_tails[i] = later_tails[i+1] * factors[i+1].tail
    terms = [(e, c*later_tails[0]) for e, c in factors[0].terms]
    prefix_degree = factors[0].degree
    for j in range(1, n):
        terms.extend((add(prefix_degree, e), c*later_tails[j])
                     for e, c in factors[j].terms if e)
        prefix_degree = add(prefix_degree, factors[j].degree)
    return from_terms(terms)


def transition(state: str, factor: Ord) -> str:
    """M: equal monomials; E: equal nonmonomials; D: distinct.

    Zero factors must be dealt with before starting the automaton.
    """
    if state not in ('M', 'E', 'D'):
        raise ValueError('Unknown state.')
    if not factor:
        raise ValueError('Use the absorbing-zero convention separately.')
    t, q = factor.tail, factor.positive_terms
    if t == 0:
        return 'M' if q == 1 else 'E'
    if t == 1:
        return state if q == 0 or state == 'D' else 'E'
    if state != 'M':
        return 'D'
    return 'M' if q == 0 else 'E'


def state_of(a: Ord, b: Ord) -> str:
    if a != b:
        return 'D'
    return 'M' if len(a.terms) == 1 else 'E'


@dataclass(frozen=True, slots=True)
class Point:
    """A point of a canonical unit CNF block of a factor."""
    block: int
    exponent: Ord
    offset: Ord
    value: Ord


def sample_points(a: Ord, offsets: Sequence[Ord]) -> list[Point]:
    points, start, block = [], ZERO, 0
    for e, c in a.terms:
        length = mono(e)
        for _ in range(c):
            for z in sorted(set(offsets)):
                if z < length:
                    points.append(Point(block, e, z, add(start, z)))
            start = add(start, length)
            block += 1
    assert all(p.value < a for p in points)
    return points


def tuple_cell(factors: Sequence[Ord], point: Sequence[Point]):
    if len(factors) != len(point) or not factors:
        raise ValueError('Expected a nonempty tuple of the appropriate arity.')
    j = 0
    for k in range(1, len(point)):
        if point[k].exponent:
            j = k
    degree = ZERO
    for a in factors[:j]:
        degree = add(degree, a.degree)
    exponent = add(degree, point[j].exponent)
    return j, exponent, point[j].block


def compare_points_by_degree(factors: Sequence[Ord], x: Sequence[Point],
                             y: Sequence[Point]) -> int:
    """Equivalent cell-degree rule, retained as a cross-check."""
    jx, ex, bx = tuple_cell(factors, x)
    jy, ey, by = tuple_cell(factors, y)
    if ex != ey:
        return -1 if ex > ey else 1
    if jx != jy:
        return -1 if jx > jy else 1
    for k in range(len(x)-1, jx, -1):
        if x[k].value != y[k].value:
            return -1 if x[k].value < y[k].value else 1
    if bx != by:
        return -1 if bx < by else 1
    for k in range(jx, -1, -1):
        if x[k].value != y[k].value:
            return -1 if x[k].value < y[k].value else 1
    return 0


def compare_points(factors: Sequence[Ord], x: Sequence[Point],
                   y: Sequence[Point]) -> int:
    """Primitive pivot comparison; no prefix ordinal arithmetic is used."""
    if len(factors) != len(x) or len(x) != len(y) or not factors:
        raise ValueError('Expected nonempty tuples of the appropriate arity.')
    jx = max((k for k in range(1, len(x)) if x[k].exponent), default=0)
    jy = max((k for k in range(1, len(y)) if y[k].exponent), default=0)
    if jx != jy:
        return -1 if jx > jy else 1
    ex, ey = x[jx].exponent, y[jy].exponent
    if ex != ey:
        return -1 if ex > ey else 1
    for k in range(len(x)-1, jx, -1):
        if x[k].value != y[k].value:
            return -1 if x[k].value < y[k].value else 1
    if x[jx].block != y[jy].block:
        return -1 if x[jx].block < y[jy].block else 1
    for k in range(jx, -1, -1):
        if x[k].value != y[k].value:
            return -1 if x[k].value < y[k].value else 1
    return 0
