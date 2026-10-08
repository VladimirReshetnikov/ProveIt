"""Resource-bounded sparse exact SU(2) compiler, with optional WL export.

This module compiles formulas. It does NOT implement a singly exponential
existential-real decision algorithm and does NOT infer knot provenance.
"""
from __future__ import annotations
from dataclasses import dataclass
from .slp import LimitExceeded, Presentation
from .degrees import profile
from .quaternion import multiply, conjugate, cross


class Ring:
    def __init__(self, nvars, *, max_terms=100000, max_pairs=10000000,
                 max_coefficient_bits=100000, check=lambda: None):
        self.nvars = nvars
        self.max_terms = max_terms
        self.max_pairs = max_pairs
        self.max_coefficient_bits = max_coefficient_bits
        self.check = check
        self.pairs = 0
        self.peak_terms = 0
        self.peak_coefficient_bits = 0
        self.zero_monomial = (0,) * nvars

    def poly(self, terms):
        self.check()
        terms = {m: c for m, c in terms.items() if c}
        if len(terms) > self.max_terms:
            raise LimitExceeded('sparse polynomial term cap')
        bits = max((abs(c).bit_length() for c in terms.values()), default=0)
        if bits > self.max_coefficient_bits:
            raise LimitExceeded('coefficient bit cap')
        self.peak_terms = max(self.peak_terms, len(terms))
        self.peak_coefficient_bits = max(self.peak_coefficient_bits, bits)
        return Poly(self, terms)

    def constant(self, c):
        return self.poly({self.zero_monomial: c})

    def variable(self, i):
        m = [0] * self.nvars
        m[i] = 1
        return self.poly({tuple(m): 1})


@dataclass
class Poly:
    ring: Ring
    terms: dict

    def coerce(self, other):
        if isinstance(other, int):
            return self.ring.constant(other)
        if not isinstance(other, Poly) or other.ring is not self.ring:
            raise TypeError('polynomial ring mismatch')
        return other

    def __add__(self, other):
        other = self.coerce(other)
        result = self.terms.copy()
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
            if not result[m]:
                del result[m]
            if len(result) > self.ring.max_terms:
                raise LimitExceeded('sparse polynomial term cap')
        return self.ring.poly(result)

    __radd__ = __add__

    def __neg__(self):
        return self.ring.poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        ring = self.ring
        count = len(self.terms) * len(other.terms)
        if ring.pairs + count > ring.max_pairs:
            raise LimitExceeded('polynomial multiplication work cap')
        ring.pairs += count
        result = {}
        for i, (m, c) in enumerate(self.terms.items()):
            if i % 128 == 0:
                ring.check()
            for n, d in other.terms.items():
                k = tuple(a + b for a, b in zip(m, n))
                result[k] = result.get(k, 0) + c*d
                if not result[k]:
                    del result[k]
                if len(result) > ring.max_terms:
                    raise LimitExceeded('sparse polynomial term cap')
                if k in result and abs(result[k]).bit_length() > ring.max_coefficient_bits:
                    raise LimitExceeded('coefficient bit cap')
        return ring.poly(result)

    __rmul__ = __mul__

    def degree(self):
        return max((sum(m) for m in self.terms), default=0)

    def evaluate(self, point):
        if len(point) != self.ring.nvars:
            raise ValueError('wrong point dimension')
        result = 0
        for monomial, coefficient in self.terms.items():
            value = coefficient
            for x, exponent in zip(point, monomial):
                value *= x**exponent
            result += value
        return result

    def wl(self):
        if not self.terms:
            return '0'
        parts = []
        for exponents, coefficient in sorted(self.terms.items()):
            factors = [str(coefficient)]
            factors.extend(f'x{i+1}' if e == 1 else f'x{i+1}^{e}'
                           for i, e in enumerate(exponents) if e)
            parts.append('*'.join(factors))
        return '(' + '+'.join(parts) + ')'


@dataclass
class Formula:
    presentation_digest: str
    ring: Ring
    residuals: tuple[Poly, ...]
    obstruction: Poly
    checkpoints: tuple[int, ...]
    delta: int

    def aggregate(self):
        h = self.ring.constant(0)
        for f in self.residuals:
            h = h + f*f
        return h

    def wolfram(self, aggregate=True):
        if aggregate:
            equalities = self.aggregate().wl() + '==0'
        else:
            equalities = ' && '.join(f.wl() + '==0' for f in self.residuals) or 'True'
        variables = ','.join(f'x{i+1}' for i in range(self.ring.nvars))
        body = equalities + ' && ' + self.obstruction.wl() + '>0'
        return ('(* Exact reference query; not a certified Renegar implementation. *)\n'
                'Resolve[Exists[{' + variables + '},' + body + '], Reals]\n')


def compile_formula(p: Presentation, checkpoints=(), *, max_degree=4096,
                    max_variables=1024, traceless=False, **ring_options) -> Formula:
    """``traceless=True`` is safe for recognition ONLY with meridian provenance."""
    if traceless and not p.meridian_generators:
        raise ValueError('traceless specialization requires meridian provenance')
    degree = profile(p, checkpoints)
    if 2 * degree.delta > max_degree:
        raise LimitExceeded('formal formula degree cap')
    if degree.dimension > max_variables:
        raise LimitExceeded('real variable count cap before allocation')
    ring = Ring(degree.dimension, **ring_options)
    zero, one = ring.constant(0), ring.constant(1)
    generators = [tuple(ring.variable(4*g + j) for j in range(4)) for g in range(p.rank)]
    residuals = [sum(q*q for q in g) - one for g in generators]
    if traceless:
        residuals.extend(g[0] for g in generators)
    checkpoint_index = {v: p.rank + i for i, v in enumerate(degree.checkpoints)}
    values = {0: (one, zero, zero, zero)}
    for v in p.live():
        rule = p.rules[v]
        if rule[0] == 't':
            g = rule[1]
            value = generators[abs(g)-1]
            if g < 0:
                value = conjugate(value)
        else:
            value = multiply(values[rule[1]], values[rule[2]])
        if v in checkpoint_index:
            offset = 4 * checkpoint_index[v]
            new = tuple(ring.variable(offset+j) for j in range(4))
            residuals.extend(x-y for x, y in zip(new, value))
            value = new
        values[v] = value
    for u, v in p.relations:
        residuals.extend(x-y for x, y in zip(values[u], values[v]))
    g = zero
    for i, q in enumerate(generators):
        for other in generators[:i]:
            for z in cross(q[1:], other[1:]):
                g = g + z*z
    return Formula(p.digest(), ring, tuple(residuals), g, degree.checkpoints, degree.delta)
