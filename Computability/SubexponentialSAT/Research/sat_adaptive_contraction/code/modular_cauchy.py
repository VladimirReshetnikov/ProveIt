#!/usr/bin/env python3
"""Finite-precision joint Cauchy features with bounded modular arithmetic.

This is a local kernel, not a SAT solver. It implements the joint crossing
factorization in the October 26 joint-Cauchy packet. The implementation uses
valuation/unit pairs, product recurrences, shared denominator inverses, and
the proved weight cutoff. Public outputs are target[mode][row] and
source[mode][column], in (Z/2^p)[U]/(U^2+U+1).

Only integer-pair inputs zeta=(a,b), representing a+b*U, are supported. This
includes nonunit and zero zeta. Every algebraic division is performed after
exact powers of two have been removed; only units are inverted modulo 2^p.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

Pair = tuple[int, int]
ZERO: Pair = (0, 0)
ONE: Pair = (1, 0)


def v2int(n: int) -> int:
    if n == 0:
        raise ValueError("valuation of zero needs a separate zero branch")
    n = abs(n)
    return (n & -n).bit_length() - 1


def split_pair(x: Pair) -> tuple[int, Pair]:
    if x == ZERO:
        raise ValueError("cannot split the zero pair")
    a, b = x
    v = min(v2int(c) for c in x if c)
    return v, (a >> v, b >> v)


class Ring:
    def __init__(self, precision: int):
        if not isinstance(precision, int) or precision < 1:
            raise ValueError("precision must be a positive integer")
        self.precision = precision
        self.mod = 1 << precision
        self.mask = self.mod - 1
        self.multiplies = 0
        self.inversions = 0

    def add(self, x: Pair, y: Pair) -> Pair:
        return ((x[0] + y[0]) & self.mask, (x[1] + y[1]) & self.mask)

    def mul(self, x: Pair, y: Pair) -> Pair:
        self.multiplies += 1
        a, b = x
        c, d = y
        return ((a*c - b*d) & self.mask, (a*d + b*c - b*d) & self.mask)

    def scale(self, x: Pair, c: int) -> Pair:
        return ((x[0]*c) & self.mask, (x[1]*c) & self.mask)

    def shift(self, x: Pair, e: int) -> Pair:
        if e < 0:
            raise ArithmeticError("negative residual valuation")
        if e >= self.precision:
            return ZERO
        return ((x[0] << e) & self.mask, (x[1] << e) & self.mask)

    def inv(self, x: Pair) -> Pair:
        self.inversions += 1
        a, b = x
        norm = (a*a - a*b + b*b) & self.mask
        if not norm & 1:
            raise ValueError("attempted inversion of a nonunit")
        r = pow(norm, -1, self.mod)
        return (((a-b)*r) & self.mask, (-b*r) & self.mask)

    def batch_inverse(self, xs: Iterable[Pair]) -> list[Pair]:
        xs = list(xs)
        if not xs:
            return []
        prefixes = [ONE]
        for x in xs:
            if not ((x[0] | x[1]) & 1):
                raise ValueError("batch contains a nonunit")
            prefixes.append(self.mul(prefixes[-1], x))
        carry = self.inv(prefixes[-1])
        result = [ZERO] * len(xs)
        for j in range(len(xs)-1, -1, -1):
            result[j] = self.mul(carry, prefixes[j])
            carry = self.mul(carry, xs[j])
        return result


@dataclass
class ModularCauchy:
    a: int
    i: int
    t: int
    zeta: Pair
    precision: int
    batch_inverses: bool = True

    def __post_init__(self):
        if self.a < 1 or not 0 <= self.i < self.a:
            raise ValueError("require a>=1 and 0<=i<a")
        self.L = 1 << self.a
        self.N = self.L // 2
        self.R = 1 << self.i
        if not -self.L <= self.t < self.L or not self.t or v2int(self.t) != self.i:
            raise ValueError("invalid grid node t")
        if len(self.zeta) != 2 or any(not isinstance(x, int) for x in self.zeta):
            raise ValueError("zeta must be an integer pair")
        self.ring = Ring(self.precision)
        self.scalar_inversions = 0
        alpha = 1 << (self.a+1)
        self.T = (self.t+alpha*self.zeta[0], alpha*self.zeta[1])
        self.T_unit = (self.T[0] >> self.i, self.T[1] >> self.i)
        self.slots = [j % self.R + 2*self.R*(j // self.R) for j in range(self.N)]
        self.exponents = [2*(b // self.R) - (b // self.R).bit_count()
                          for b in range(self.N)]
        self.weights = [self.a+1-self.i+2*e for e in self.exponents]
        self.B = next((b for b, w in enumerate(self.weights)
                       if w >= self.precision), self.N)
        self._den: dict[int, tuple[int, Pair, Pair]] = {}

    def prepare_denominators(self, B: int):
        """Reuse O(L) distinct denominators rather than inverting per entry."""
        diffs = sorted({sign*(self.slots[j]-self.slots[b])
                        for b in range(B) for j in range(b, self.N)
                        for sign in (-1, 1)})
        vals, units = [], []
        for d in diffs:
            v, unit = split_pair((self.T[0]+d, self.T[1]))
            if v > self.i:
                raise ArithmeticError("crossing denominator bound failed")
            vals.append(v)
            units.append(unit)
        inverse = (self.ring.batch_inverse(units) if self.batch_inverses
                   else [self.ring.inv(x) for x in units])
        self._den = {d: (v, inv, self.ring.mul(self.T_unit, inv))
                     for d, v, inv in zip(diffs, vals, inverse)}

    def prefactor(self) -> Pair:
        """C(T)/(C'(0)T), with the q=0 factor cancelled symbolically."""
        num_unit, den_unit, exponent = ONE, 1, 0
        for q in range(-self.L, self.L):
            if q == 0:
                continue
            raw = (self.T[0]-q, self.T[1])
            if raw == ZERO:
                return ZERO
            vn, un = split_pair(raw)
            vd = v2int(q)
            exponent += vn-vd
            num_unit = self.ring.mul(num_unit, un)
            den_unit = (den_unit * ((-q) >> vd)) & self.ring.mask
        if exponent < self.a+1-self.i:
            raise ArithmeticError("prefactor valuation bound failed")
        self.scalar_inversions += 1
        return self.ring.shift(self.ring.scale(num_unit,
                               pow(den_unit, -1, self.ring.mod)), exponent)

    def iter_columns(self, truncate: bool = True):
        """Stream (index,target-column,source-column) using O(L+B) ring storage."""
        B = self.B if truncate else self.N
        self.prepare_denominators(B)
        pref = self.prefactor()
        ring = self.ring
        for j, x in enumerate(self.slots):
            target = [ZERO]*B
            source = [ZERO]*B
            # P_b and Q_b products, maintained as 2^v times a unit.
            pv = qv = 0
            pu = qu = ONE
            for b in range(min(j+1, B)):
                d = x-self.slots[b]
                vd, invd, td = self._den[d]
                vm, invm, tm = self._den[-d]
                e = self.exponents[b]
                row = ring.shift(ring.mul(pu, td),
                                 pv+self.i-vd-e)
                col = ring.shift(ring.mul(qu, tm),
                                 qv+self.i-vm-e)
                target[b] = ring.mul(pref, ring.shift(row, 2*e))
                source[b] = col
                if d:
                    vn = v2int(d)
                    du = d >> vn
                    pv += vn-vd
                    qv += vn-vm
                    pu = ring.mul(pu, ring.scale(invd, du))
                    qu = ring.mul(qu, ring.scale(invm, -du))
            yield j, target, source

    def feature_tables(self, truncate: bool = True) -> tuple[list[list[Pair]], list[list[Pair]]]:
        B = self.B if truncate else self.N
        target = [[ZERO]*self.N for _ in range(B)]
        source = [[ZERO]*self.N for _ in range(B)]
        for j, tc, sc in self.iter_columns(truncate):
            for b in range(B):
                target[b][j] = tc[b]
                source[b][j] = sc[b]
        return target, source

    def direct_entry(self, row: int, column: int) -> Pair:
        d = self.slots[row]-self.slots[column]
        v, unit = split_pair((self.T[0]+d, self.T[1]))
        ratio = self.ring.shift(self.ring.mul(self.T_unit, self.ring.inv(unit)), self.i-v)
        return self.ring.mul(self.prefactor(), ratio)


def reconstruct(target, source, row, column, ring: Ring) -> Pair:
    value = ZERO
    for b in range(len(target)):
        value = ring.add(value, ring.mul(target[b][row], source[b][column]))
    return value
