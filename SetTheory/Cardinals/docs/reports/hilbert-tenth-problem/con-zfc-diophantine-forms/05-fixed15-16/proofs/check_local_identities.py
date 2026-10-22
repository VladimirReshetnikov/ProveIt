#!/usr/bin/env python3
"""Exact sparse-coefficient checks of the local polynomial identities.

This is intentionally independent of the arithmetic circuit generator.
It proves the displayed algebraic cuts over Z, not the Pell/compiler theorem.
Only Python's standard library is used. No assertions disappear under -O.
"""
from __future__ import annotations
import json


class Poly:
    def __init__(self, terms, arity):
        self.terms = {m: c for m, c in terms.items() if c}
        self.arity = arity

    def coerce(self, value):
        if isinstance(value, Poly):
            if self.arity != value.arity:
                raise ValueError('incompatible polynomial rings')
            return value
        if type(value) is not int:
            raise TypeError('integer coefficient required')
        return Poly({(0,)*self.arity: value}, self.arity)

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for m, c in other.terms.items():
            terms[m] = terms.get(m, 0)+c
        return Poly(terms, self.arity)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()}, self.arity)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        terms = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                power = tuple(x+y for x, y in zip(m, n))
                terms[power] = terms.get(power, 0)+c*d
        return Poly(terms, self.arity)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError('nonnegative integer exponent required')
        result = self.coerce(1)
        for _ in range(exponent):
            result = result*self
        return result


def ring(names):
    arity = len(names)
    out = []
    for j in range(arity):
        m = tuple(int(i == j) for i in range(arity))
        out.append(Poly({m: 1}, arity))
    return out


def verify():
    checks = {}

    def equal(name, left, right):
        difference = left-right
        if difference.terms:
            raise ValueError('nonzero coefficient in '+name)
        checks[name] = {'equal': True, 'expanded_monomials': len(left.terms)}

    X, a, c, H, g = ring(['X', 'a', 'c', 'H', 'g'])
    equal('main_norm_cancellation',
          (X+a*c+g)**2-(a*a+H)*c*c,
          X*X+2*X*g+g*g+2*a*c*X+2*a*c*g-H*c*c)

    X, Y, k = ring(['X', 'Y', 'k'])
    E = X*Y
    L = E*k*Y
    equal('factored_first_norm', L*(L+k), (E*E+X)*(k*Y)**2)
    equal('first_norm_alternate', L*(L+k), X*Y**2*(X*Y**2+1)*k*k)

    Delta, f, i, c = ring(['Delta', 'f', 'i', 'c'])
    Q = (Delta*i*c*c)**2
    equal('reduced_auxiliary_coefficient_mod_strong_equation',
          Delta*(f*f-1)-Q, Delta*(f*f-Delta*i*i*c**4-1))
    equal('scaled_strong_factor', Delta*f*f-Q,
          Delta*(f*f-Delta*i*i*c**4))

    Q, D, v, z, y, f = ring(['Q', 'D', 'v', 'z', 'y', 'f'])
    A = Q*(D*v*v+z*z-y*y)+y*y-1
    B = 2*Q*v*z
    equal('root_restoration_mod_f_square',
          Q*((v*f-z)**2-y*y)+y*y-(A+1-B*f), Q*v*v*(f*f-D))
    equal('shared_norm_discriminant', D*B*B, 4*(Q*D*v*v)*(Q*z*z))

    P, A, B, D = ring(['P', 'A', 'B', 'D'])
    equal('outer_norm_unit_expansion',
          (P*(A+1)-1)**2-D*(P*B)**2,
          P*(P*((A+1)**2-D*B*B)-2*(A+1))+1)
    return {'status': 'PASS', 'identities': checks,
            'scope': 'Exact formal sparse coefficient equalities over Z; not a proof of the quantified compiler/Pell equivalence.'}


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
