#!/usr/bin/env python3
"""Division-free weighted distribution normal forms (Python >= 3.10).

All polynomial and certificate computations use Python integers only.
Point a denotes a/q modulo 1, including the formal point 0.
No evaluation of a transcendental number is used in this module.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, prod
from typing import Callable, Mapping


@lru_cache(maxsize=None)
def factor(n: int) -> tuple[tuple[int, int], ...]:
    if not isinstance(n, int) or n < 1:
        raise ValueError("factor requires a positive integer")
    out = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def phi(q: int) -> int:
    return prod(p ** (e - 1) * (p - 1) for p, e in factor(q))


@dataclass(frozen=True)
class Poly:
    """Sparse integer polynomial; entries are (exponent tuple, coefficient)."""
    arity: int
    terms: tuple[tuple[tuple[int, ...], int], ...] = ()

    @staticmethod
    def make(arity: int, terms: Mapping[tuple[int, ...], int]) -> 'Poly':
        if arity < 0 or any(len(m) != arity or any(e < 0 for e in m)
                            or not isinstance(c, int) for m, c in terms.items()):
            raise ValueError("invalid polynomial")
        return Poly(arity, tuple(sorted((m, c) for m, c in terms.items() if c)))

    @staticmethod
    def constant(arity: int, n: int) -> 'Poly':
        return Poly.make(arity, {(0,) * arity: n})

    @staticmethod
    def variable(arity: int, i: int) -> 'Poly':
        if not 0 <= i < arity:
            raise ValueError("invalid variable index")
        m = [0] * arity
        m[i] = 1
        return Poly.make(arity, {tuple(m): 1})

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __neg__(self) -> 'Poly':
        return Poly(self.arity, tuple((m, -c) for m, c in self.terms))

    def __add__(self, other: 'Poly') -> 'Poly':
        if self.arity != other.arity:
            raise ValueError("polynomial rings differ")
        d = dict(self.terms)
        for m, c in other.terms:
            d[m] = d.get(m, 0) + c
        return Poly.make(self.arity, d)

    def __sub__(self, other: 'Poly') -> 'Poly':
        return self + (-other)

    def __mul__(self, other: 'Poly') -> 'Poly':
        if self.arity != other.arity:
            raise ValueError("polynomial rings differ")
        d: dict[tuple[int, ...], int] = {}
        for m, c in self.terms:
            for n, b in other.terms:
                mn = tuple(x + y for x, y in zip(m, n))
                d[mn] = d.get(mn, 0) + c * b
        return Poly.make(self.arity, d)

    def evaluate(self, values: tuple[int, ...]) -> int:
        if len(values) != self.arity:
            raise ValueError("wrong number of values")
        return sum(c * prod(v ** e for v, e in zip(values, m)) for m, c in self.terms)

    def encode(self) -> list:
        return [[list(m), c] for m, c in self.terms]

    @staticmethod
    def decode(arity: int, obj: list) -> 'Poly':
        if not isinstance(obj, list):
            raise ValueError("polynomial must be a list")
        terms = {}
        for item in obj:
            if (not isinstance(item, list) or len(item) != 2
                    or not isinstance(item[0], list)
                    or len(item[0]) != arity
                    or any(type(e) is not int or e < 0 for e in item[0])
                    or type(item[1]) is not int):
                raise ValueError("invalid polynomial encoding")
            m, c = tuple(item[0]), item[1]
            if m in terms:
                raise ValueError("duplicate monomial")
            terms[m] = c
        return Poly.make(arity, terms)


def add_scaled(out: dict, vector: Mapping, scale: Poly) -> None:
    """out += scale * vector, dropping zero entries."""
    for key, value in vector.items():
        v = scale * value
        out[key] = out[key] + v if key in out else v
        if not out[key]:
            del out[key]


class Distribution:
    """Universal Z[A_p]-module and exact raw-row certificates at one level."""
    def __init__(self, q: int):
        if type(q) is not int or q < 1:
            raise ValueError("level must be a positive integer")
        self.q = q
        self.primes = tuple(p for p, _ in factor(q))
        self.arity = len(self.primes)
        self.one = Poly.constant(self.arity, 1)
        self.zero = Poly.constant(self.arity, 0)
        self.A = {p: Poly.variable(self.arity, i) for i, p in enumerate(self.primes)}
        self.basis = tuple(a for a in range(q) if not self.bad_primes(a))
        self.index = {a: i for i, a in enumerate(self.basis)}
        # Per-instance memoizers avoid retaining instances globally.
        self.normal_form = lru_cache(maxsize=None)(self._normal_form)
        self.certificate = lru_cache(maxsize=None)(self._certificate)

    def conductor(self, a: int) -> int:
        return self.q // gcd(self.q, a % self.q)

    def bad_primes(self, a: int) -> tuple[int, ...]:
        a %= self.q
        if not a:
            return ()
        g = gcd(self.q, a)
        m, n = self.q // g, a // g
        out = []
        for p, e in factor(m):
            pe = p ** e
            b = n * pow(m // pe, -1, pe) % pe
            if (e == 1 and b == 1) or (e > 1 and b < p ** (e - 1)):
                out.append(p)
        return tuple(out)

    def order_key(self, a: int) -> tuple[int, int, int]:
        return self.conductor(a), len(self.bad_primes(a)), a

    def row(self, p: int, x: int) -> dict[int, Poly]:
        """r_(p,x) = sum_(p*y=x) e_y - A_p e_x. x is a grid index."""
        if p not in self.A or type(x) is not int or not 0 <= x < self.q or x % p:
            raise ValueError("invalid prime row")
        out: dict[int, Poly] = {}
        a = x // p
        for j in range(p):
            add_scaled(out, {(a + j * (self.q // p)) % self.q: self.one}, self.one)
        add_scaled(out, {x: self.one}, -self.A[p])
        return out

    def rows(self):
        for p in self.primes:
            for x in range(0, self.q, p):
                yield p, x, self.row(p, x)

    def _normal_form(self, a: int) -> dict[int, Poly]:
        if not 0 <= a < self.q:
            raise ValueError("point index out of range")
        bad = self.bad_primes(a)
        if not bad:
            return {a: self.one}
        p = bad[0]
        out: dict[int, Poly] = {}
        add_scaled(out, self.normal_form(p * a % self.q), self.A[p])
        for j in range(1, p):
            z = (a + j * (self.q // p)) % self.q
            add_scaled(out, self.normal_form(z), -self.one)
        return out

    def _certificate(self, a: int) -> dict[tuple[int, int], Poly]:
        """C with e_a - NF(e_a) = sum C[p,x] r_(p,x)."""
        bad = self.bad_primes(a)
        if not bad:
            return {}
        p = bad[0]
        out = {(p, p * a % self.q): self.one}
        add_scaled(out, self.certificate(p * a % self.q), self.A[p])
        for j in range(1, p):
            z = (a + j * (self.q // p)) % self.q
            add_scaled(out, self.certificate(z), -self.one)
        return out

    def reduce_vector(self, vector: Mapping[int, Poly]) -> dict[int, Poly]:
        out: dict[int, Poly] = {}
        for a, c in vector.items():
            add_scaled(out, self.normal_form(a), c)
        return out

    def check_unit_minor(self) -> int:
        """Checks the selected square minor is triangular with diagonal 1."""
        pivots = sorted((a for a in range(self.q) if self.bad_primes(a)), key=self.order_key)
        positions = {a: i for i, a in enumerate(pivots)}
        rows = set()
        for a in pivots:
            p = self.bad_primes(a)[0]
            row_id = p, p * a % self.q
            if row_id in rows:
                raise AssertionError("selected rows are not distinct")
            rows.add(row_id)
            row = self.row(*row_id)
            if row.get(a) != self.one:
                raise AssertionError("pivot not equal to 1")
            if any(z in positions and positions[z] > positions[a] for z in row):
                raise AssertionError("minor not triangular")
        if len(pivots) != self.q - phi(self.q):
            raise AssertionError("wrong basis size")
        return len(pivots)

    def reflection_columns(self) -> list[dict[int, Poly]]:
        return [self.normal_form(-a % self.q) for a in self.basis]


def rank_binary(columns: list[int]) -> int:
    """Exact F_2 rank of bit-encoded columns."""
    pivots: dict[int, int] = {}
    for a in columns:
        while a:
            bit = a.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = a
                break
            a ^= pivots[bit]
    return len(pivots)


def active_count(q: int) -> int:
    f = dict(factor(q))
    return sum(p != 2 for p in f) + int(f.get(2, 0) >= 2)


def reflected_torsion(q: int, weights: Mapping[int, int]) -> int:
    if q <= 2:
        raise ValueError("the balanced formula is for q > 2")
    if any(weights[p] % 2 == 0 for p, _ in factor(q) if p != 2):
        return 0
    return 2 ** (active_count(q) - 1)
