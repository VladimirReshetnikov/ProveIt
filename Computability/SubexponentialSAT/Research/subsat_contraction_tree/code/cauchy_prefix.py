#!/usr/bin/env python3
"""Linear-work generation of full-crossing Cauchy features modulo powers of two.

A local exact kernel, not a SAT solver. Standard-library Python, integer
coordinates for the unramified quadratic lift U^2+U+1=0. The mathematical
feature formulas are those of the reviewed JointCauchyKernel; this module
changes their evaluation algorithm, not their mode weights.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterator

Pair = tuple[int, int]

def ord2(n: int) -> int:
    if n == 0:
        raise ValueError('ord2(0) is undefined')
    n = abs(n)
    return (n & -n).bit_length() - 1

@dataclass
class Work:
    multiplications: int = 0
    unit_inversions: int = 0
    integer_factorizations: int = 0
    emitted_modes: int = 0

class QuadraticRing:
    def __init__(self, precision: int, work: Work | None = None):
        if not isinstance(precision, int) or precision < 1:
            raise ValueError('precision must be positive')
        self.precision = precision
        self.modulus = 1 << precision
        self.mask = self.modulus - 1
        self.work = work if work is not None else Work()

    def mul(self, x: Pair, y: Pair) -> Pair:
        self.work.multiplications += 1
        a, b = x; c, d = y
        return ((a*c-b*d) & self.mask, (a*d+b*c-b*d) & self.mask)

    def inv(self, x: Pair) -> Pair:
        self.work.unit_inversions += 1
        a, b = x
        norm = (a*a-a*b+b*b) & self.mask
        if not norm & 1:
            raise ValueError('a nonunit was passed to unit inversion')
        ni = pow(norm, -1, self.modulus)
        return (((a-b)*ni) & self.mask, (-b*ni) & self.mask)

    def shift(self, x: Pair, valuation: int) -> Pair:
        if valuation < 0:
            raise ArithmeticError('negative total valuation')
        if valuation >= self.precision:
            return (0, 0)
        return ((x[0] << valuation) & self.mask,
                (x[1] << valuation) & self.mask)

    def split(self, x: Pair) -> tuple[int, Pair] | None:
        """Factor exact integer coordinates before reduction, never divide a residue."""
        self.work.integer_factorizations += 1
        a, b = x
        if a == b == 0:
            return None
        v = min(ord2(z) for z in x if z)
        return v, ((a >> v) & self.mask, (b >> v) & self.mask)

class PrefixKernel:
    def __init__(self, a: int, i: int, t: int, precision: int,
                 zeta: Pair = (0, 1), work: Work | None = None):
        if not isinstance(a, int) or a < 1 or not 0 <= i < a:
            raise ValueError('require a>=1 and 0<=i<a')
        self.a, self.i, self.t = a, i, t
        self.L, self.R = 1 << a, 1 << i
        self.N = self.L // 2
        if not isinstance(t, int) or not -self.L <= t < self.L or not t or ord2(t) != i:
            raise ValueError('t must be a grid point of valuation i')
        if len(zeta) != 2 or any(not isinstance(x, int) for x in zeta):
            raise ValueError('zeta requires two integer coordinates')
        self.zeta = zeta
        alpha = 1 << (a+1)
        self.T = (t + alpha*zeta[0], alpha*zeta[1])
        self.ring = QuadraticRing(precision, work)
        self._T_split = self.ring.split(self.T)
        if self._T_split is None or self._T_split[0] != i:
            raise ArithmeticError('T has the wrong valuation')
        self._prefactor: Pair | None = None

    def slot(self, j: int) -> int:
        if not isinstance(j, int) or not 0 <= j < self.N:
            raise ValueError('port index outside packet')
        return j % self.R + 2*self.R*(j//self.R)

    def E(self, b: int) -> int:
        q = b//self.R
        return 2*q - q.bit_count()

    def weight(self, b: int) -> int:
        return self.a+1-self.i + 2*self.E(b)

    def _ratio(self, difference: int, numerator: str) -> tuple[int, Pair]:
        """Factored T/(T+d) or d/(T+d); all inversions are of units."""
        denominator = self.ring.split((self.T[0]+difference, self.T[1]))
        if denominator is None:
            raise ArithmeticError('zero crossing denominator')
        dv, du = denominator
        if numerator == 'T':
            nv, nu = self._T_split
        elif numerator == 'd':
            if difference == 0:
                raise ValueError('zero difference is handled by triangular support')
            nv = ord2(difference)
            nu = ((difference >> nv) & self.ring.mask, 0)
            self.ring.work.integer_factorizations += 1
        else:
            raise ValueError('unknown ratio numerator')
        if nv < dv:
            raise ArithmeticError('nonintegral crossing ratio')
        return nv-dv, self.ring.mul(nu, self.ring.inv(du))

    def prefactor(self) -> Pair:
        """C(T)/(C'(0)T), evaluated once with exact valuation cancellation."""
        if self._prefactor is not None:
            return self._prefactor
        num_unit, den_unit = (1, 0), 1
        valuation = 0
        for q in range(-self.L, self.L):
            if q == 0:
                continue
            sf = self.ring.split((self.T[0]-q, self.T[1]))
            if sf is None:
                self._prefactor = (0, 0)
                return self._prefactor
            nv, nu = sf
            den = -q
            dv = ord2(den)
            valuation += nv-dv
            num_unit = self.ring.mul(num_unit, nu)
            den_unit = (den_unit*(den >> dv)) & self.ring.mask
        if valuation < 0:
            raise ArithmeticError('nonintegral prefactor')
        self._prefactor = self.ring.shift(
            self.ring.mul(num_unit, self.ring.inv((den_unit, 0))), valuation)
        return self._prefactor

    def features(self, index: int, modes: int, *, method: str = 'prefix',
                 truncate: bool = True) -> Iterator[tuple[int, Pair, Pair]]:
        """Yield (mode, target, source); use constant auxiliary ring storage.

        Direct control recomputes each product from scratch in the same ring.
        Prefix mode maintains unit/valuation pairs, so normalization by 2^E
        never requires dividing an already reduced modular value.
        """
        x = self.slot(index)
        if not isinstance(modes, int) or not 0 <= modes <= self.N:
            raise ValueError('invalid mode count')
        if method not in ('prefix', 'direct'):
            raise ValueError('unknown evaluation method')
        pre = self.prefactor()
        row_unit = source_unit = (1, 0)
        row_v = source_v = 0
        for b in range(modes):
            self.ring.work.emitted_modes += 1
            if b > index or (truncate and self.weight(b) >= self.ring.precision):
                yield b, (0, 0), (0, 0)
                continue
            if method == 'direct':
                row_unit = source_unit = (1, 0)
                row_v = source_v = 0
                for h in range(b):
                    d = x-self.slot(h)
                    rv, ru = self._ratio(d, 'd')
                    sv, su = self._ratio(-d, 'd')
                    row_v += rv; source_v += sv
                    row_unit = self.ring.mul(row_unit, ru)
                    source_unit = self.ring.mul(source_unit, su)
            d = x-self.slot(b)
            rv, ru = self._ratio(d, 'T')
            sv, su = self._ratio(-d, 'T')
            row = self.ring.shift(self.ring.mul(row_unit, ru), row_v+rv-self.E(b))
            source = self.ring.shift(self.ring.mul(source_unit, su), source_v+sv-self.E(b))
            target = self.ring.mul(pre, self.ring.shift(row, 2*self.E(b)))
            yield b, target, source
            if method == 'prefix' and b < index:
                rv, ru = self._ratio(d, 'd')
                sv, su = self._ratio(-d, 'd')
                row_v += rv; source_v += sv
                row_unit = self.ring.mul(row_unit, ru)
                source_unit = self.ring.mul(source_unit, su)

    def entry(self, row: int, column: int) -> Pair:
        d = self.slot(row)-self.slot(column)
        v, u = self._ratio(d, 'T')
        return self.ring.mul(self.prefactor(), self.ring.shift(u, v))


def collect(kernel: PrefixKernel, indices: list[int], modes: int,
            method: str = 'prefix', truncate: bool = True) -> list[list[tuple[int, Pair, Pair]]]:
    return [list(kernel.features(j, modes, method=method, truncate=truncate)) for j in indices]
