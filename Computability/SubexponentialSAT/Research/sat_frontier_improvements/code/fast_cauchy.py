#!/usr/bin/env python3
"""Quadratic-time full crossing-block Cauchy features modulo 2**p.

Exact local kernel, not an end-to-end SAT solver.  Standard library only.
The ring is (Z/2**p Z)[U]/(U**2+U+1). Integer zeta coordinates are immutable
lifts. Valuation/unit states are retained even when their displayed residue
vanishes; a subsequent recurrence may lower the valuation.
"""
from dataclasses import dataclass
from math import inf


def v2_int(n):
    if n == 0:
        return inf
    n = abs(n)
    return (n & -n).bit_length() - 1


class Ring:
    def __init__(self, precision):
        if not isinstance(precision, int) or precision < 1:
            raise ValueError('precision must be a positive integer')
        self.precision = precision
        self.modulus = 1 << precision
        self.mask = self.modulus - 1
        self.multiplications = 0
        self.inversions = 0

    def mul(self, x, y):
        self.multiplications += 1
        a, b = x
        c, d = y
        return ((a*c-b*d) & self.mask, (a*d+b*c-b*d) & self.mask)

    def inv(self, x):
        a, b = x
        norm = (a*a-a*b+b*b) & self.mask
        if not norm & 1:
            raise ValueError('only units may be inverted')
        self.inversions += 1
        z = pow(norm, -1, self.modulus)
        return (((a-b)*z) & self.mask, (-b*z) & self.mask)

    def scale(self, unit, valuation):
        if valuation < 0:
            raise ArithmeticError('nonintegral feature')
        if valuation >= self.precision:
            return (0, 0)
        return ((unit[0] << valuation) & self.mask,
                (unit[1] << valuation) & self.mask)

    def normalize(self, x):
        valuation = min(v2_int(x[0]), v2_int(x[1]))
        if valuation == inf:
            raise ValueError('zero has no unit part')
        return valuation, ((x[0] >> valuation) & self.mask,
                           (x[1] >> valuation) & self.mask)

    def batch_inverse(self, values):
        """One inversion and O(len(values)) products, valid in this ring."""
        if not values:
            return []
        prefixes = [(1, 0)]
        for value in values:
            prefixes.append(self.mul(prefixes[-1], value))
        carry = self.inv(prefixes[-1])
        result = [(0, 0)] * len(values)
        for j in range(len(values)-1, -1, -1):
            result[j] = self.mul(carry, prefixes[j])
            carry = self.mul(carry, values[j])
        return result


@dataclass
class Tables:
    target: list
    source: list
    stats: dict


class FastCauchy:
    def __init__(self, a, i, t, precision, zeta=(1, 0)):
        if not isinstance(a, int) or a < 1 or not 0 <= i < a:
            raise ValueError('require a >= 1 and 0 <= i < a')
        if not -(1 << a) <= t < (1 << a) or v2_int(t) != i:
            raise ValueError('invalid nonzero retained interpolation node')
        if len(zeta) != 2 or any(not isinstance(x, int) for x in zeta):
            raise ValueError('zeta must have two integer lift coordinates')
        self.a, self.i, self.t = a, i, t
        self.L, self.R, self.N = 1 << a, 1 << i, 1 << (a-1)
        self.ring = Ring(precision)
        self.zeta = tuple(zeta)
        alpha = 1 << (a+1)
        self.T = (t+alpha*zeta[0], alpha*zeta[1])
        self.tv, self.tu = self.ring.normalize(self.T)
        self.slots = [j % self.R + 2*self.R*(j//self.R) for j in range(self.N)]
        self.energies = [2*(b//self.R)-(b//self.R).bit_count() for b in range(self.N)]
        self._prepare()

    def _prepare(self):
        ring = self.ring
        # Difference set of S={r+2Rq: 0<=r<R, 0<=q<N/R}; O(L) entries.
        J = self.N // self.R
        deltas = [2*self.R*q+r for q in range(1-J, J)
                  for r in range(1-self.R, self.R)]
        units, self.denval = [], {}
        for delta in deltas:
            value, unit = ring.normalize((self.T[0]+delta, self.T[1]))
            if value > self.i:
                raise ArithmeticError('crossing denominator valuation bound failed')
            self.denval[delta] = value
            units.append(unit)
        # Cancel the q=0 factor T before constructing Gamma(T)/T.
        numerator_unit = (1, 0)
        denominator_unit = 1
        numerator_valuation = denominator_valuation = 0
        zero_prefactor = False
        for q in range(-self.L, self.L):
            if q == 0:
                continue
            pair = (self.T[0]-q, self.T[1])
            if pair == (0, 0):
                zero_prefactor = True
            else:
                val, unit = ring.normalize(pair)
                numerator_valuation += val
                numerator_unit = ring.mul(numerator_unit, unit)
            dv = v2_int(q)
            denominator_valuation += dv
            denominator_unit = (denominator_unit*((-q) >> dv)) & ring.mask
        inverses = ring.batch_inverse(units+[(denominator_unit, 0)])
        self.deninv = dict(zip(deltas, inverses[:-1]))
        self.prefv = numerator_valuation-denominator_valuation
        self.prefu = ring.mul(numerator_unit, inverses[-1])
        if zero_prefactor:
            self.prefv, self.prefu = ring.precision, (0, 0)
        elif self.prefv < self.a+1-self.i:
            raise ArithmeticError('prefactor divisibility failed')
        self.preparation_multiplications = ring.multiplications
        self.unique_denominators = len(deltas)

    def direct_entry(self, row, column):
        if not 0 <= row < self.N or not 0 <= column < self.N:
            raise ValueError('matrix index out of range')
        delta = self.slots[row]-self.slots[column]
        unit = self.ring.mul(self.prefu, self.ring.mul(self.tu, self.deninv[delta]))
        return self.ring.scale(unit, self.prefv+self.tv-self.denval[delta])

    def _start(self, j, sign):
        delta = sign*self.slots[j]
        return self.tv-self.denval[delta], self.ring.mul(self.tu, self.deninv[delta])

    def _next(self, b, j, sign, value, unit):
        delta = sign*(self.slots[j]-self.slots[b])
        next_delta = sign*(self.slots[j]-self.slots[b+1])
        nv = v2_int(delta)
        value += nv-self.denval[next_delta]-(self.energies[b+1]-self.energies[b])
        unit = self.ring.mul(unit, ((delta >> nv) & self.ring.mask, 0))
        unit = self.ring.mul(unit, self.deninv[next_delta])
        if value < 0:
            raise ArithmeticError('normalized recurrence lost integrality')
        return value, unit

    def feature_tables(self):
        ring, N = self.ring, self.N
        target = [[(0, 0)]*N for _ in range(N)]
        source = [[(0, 0)]*N for _ in range(N)]
        before = ring.multiplications
        transitions = 0
        for j in range(N):
            rv, ru = self._start(j, 1)
            sv, su = self._start(j, -1)
            for b in range(j+1):
                target[b][j] = ring.scale(ring.mul(self.prefu, ru), self.prefv+2*self.energies[b]+rv)
                source[b][j] = ring.scale(su, sv)
                if b < j:
                    rv, ru = self._next(b, j, 1, rv, ru)
                    sv, su = self._next(b, j, -1, sv, su)
                    transitions += 2
        return Tables(target, source, {
            'dimension': N, 'precision': ring.precision,
            'unit_inversions': ring.inversions,
            'unique_denominators': self.unique_denominators,
            'preparation_multiplications': self.preparation_multiplications,
            'table_multiplications': ring.multiplications-before,
            'recurrence_transitions': transitions})

    def naive_feature_tables(self):
        """Matched finite-ring direct-product baseline; deliberately cubic.

        Uses the same cached denominators and precision. Thus comparison
        isolates prefix reuse, rather than rational versus modular arithmetic.
        """
        ring, N = self.ring, self.N
        target = [[(0, 0)]*N for _ in range(N)]
        source = [[(0, 0)]*N for _ in range(N)]
        before = ring.multiplications
        product_steps = 0
        for b in range(N):
            for j in range(b, N):
                for sign, table in ((1, target), (-1, source)):
                    delta = sign*(self.slots[j]-self.slots[b])
                    value = self.tv-self.denval[delta]-self.energies[b]
                    unit = ring.mul(self.tu, self.deninv[delta])
                    for h in range(b):
                        diff = sign*(self.slots[j]-self.slots[h])
                        nv = v2_int(diff)
                        value += nv-self.denval[diff]
                        unit = ring.mul(unit, ((diff >> nv) & ring.mask, 0))
                        unit = ring.mul(unit, self.deninv[diff])
                        product_steps += 1
                    if sign == 1:
                        table[b][j] = ring.scale(ring.mul(self.prefu, unit), self.prefv+2*self.energies[b]+value)
                    else:
                        table[b][j] = ring.scale(unit, value)
        return Tables(target, source, {
            'dimension': N, 'precision': ring.precision,
            'unit_inversions': ring.inversions,
            'unique_denominators': self.unique_denominators,
            'preparation_multiplications': self.preparation_multiplications,
            'table_multiplications': ring.multiplications-before,
            'direct_product_steps': product_steps})


def reconstruct(tables, ring, row, column):
    total = (0, 0)
    for b in range(min(row, column)+1):
        a, c = ring.mul(tables.target[b][row], tables.source[b][column])
        total = ((total[0]+a) & ring.mask, (total[1]+c) & ring.mask)
    return total
