#!/usr/bin/env python3
"""Exact finite regression checks accompanying article.tex (Python >= 3.9).

Only rational Laurent polynomials and finite power-series jets are represented.
This is not a surreal-number implementation or a proof checker.
"""
from __future__ import annotations
import argparse
import json
import platform
import random
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Dict

@dataclass(frozen=True)
class G:
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def of(x):
        return x if isinstance(x, G) else G(F(x))
    def __add__(self, other):
        q = G.of(other)
        return G(self.re + q.re, self.im + q.im)
    __radd__ = __add__
    def __neg__(self):
        return G(-self.re, -self.im)
    def __sub__(self, other):
        return self + (-G.of(other))
    def __rsub__(self, other):
        return G.of(other) - self
    def __mul__(self, other):
        q = G.of(other)
        return G(self.re*q.re - self.im*q.im, self.re*q.im + self.im*q.re)
    __rmul__ = __mul__
    def __truediv__(self, other):
        q = G.of(other)
        d = q.re*q.re + q.im*q.im
        if not d:
            raise ZeroDivisionError('Gaussian-rational division by zero')
        return self * G(q.re/d, -q.im/d)
    def __pow__(self, n: int):
        if n < 0:
            return (G(1)/self) ** (-n)
        ans, base = G(1), self
        while n:
            if n & 1:
                ans = ans*base
            base, n = base*base, n//2
        return ans
    def __bool__(self):
        return bool(self.re or self.im)
    def conjugate(self):
        return G(self.re, -self.im)

Poly = Dict[F, G]
I = G(0, 1)
ONE: Poly = {F(0): G(1)}

def clean(p: Poly) -> Poly:
    return {F(k): G.of(v) for k, v in p.items() if v}

def add(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, G()) + v
    return clean(r)

def scale(p: Poly, c) -> Poly:
    return clean({k: v*G.of(c) for k, v in p.items()})

def mul(p: Poly, q: Poly, cutoff=None) -> Poly:
    r: Poly = {}
    for j, a in p.items():
        for k, b in q.items():
            e = j+k
            if cutoff is None or e <= cutoff:
                r[e] = r.get(e, G()) + a*b
    return clean(r)

def jet(p: Poly, cutoff: int) -> Poly:
    return {k: v for k, v in p.items() if k <= cutoff}

def derivative(p: Poly) -> Poly:
    """The normalized surreal derivation: D(t^q)=-q*t^(q+1)."""
    return clean({q+1: c*(-q) for q, c in p.items() if q != 0})

def primitive(p: Poly):
    """Return (Laurent part, coefficient of log(omega))."""
    a = {q-1: c/(1-q) for q, c in p.items() if q != 1}
    return clean(a), p.get(F(1), G())

def exp_jet(h: Poly, cutoff: int) -> Poly:
    if h and min(h) <= 0:
        raise ValueError('exp_jet requires strictly positive exponents')
    term, result, n = ONE, ONE, 0
    while term:
        n += 1
        term = scale(mul(term, h, cutoff), F(1, n))
        result = add(result, term)
    return result

def random_poly(rng, rational_exponents=True, real_only=False):
    p: Poly = {}
    for _ in range(rng.randrange(1, 9)):
        exponent = F(rng.randrange(-16, 25), 4 if rational_exponents else 1)
        coefficient = G(F(rng.randrange(-6, 7), rng.randrange(1, 6)),
                        0 if real_only else F(rng.randrange(-6, 7), rng.randrange(1, 6)))
        p[exponent] = p.get(exponent, G()) + coefficient
    return clean(p)

def run():
    rng = random.Random(20260921)
    counts = {}
    def check(category, condition):
        counts[category] = counts.get(category, 0) + 1
        if not condition:
            raise AssertionError(f'{category}: check {counts[category]} failed')
    for _ in range(250):
        p, q = random_poly(rng), random_poly(rng)
        check('Leibniz rule', derivative(mul(p, q)) == add(mul(derivative(p), q), mul(p, derivative(q))))
        check('Additivity', derivative(add(p, q)) == add(derivative(p), derivative(q)))
        a, ell = primitive(p)
        check('Primitive including logarithmic term', add(derivative(a), {F(1):ell} if ell else {}) == p)
        check('Conjugation compatibility', derivative({k:v.conjugate() for k,v in p.items()}) == {k:v.conjugate() for k,v in derivative(p).items()})
    for numerator in range(-20, 29):
        q = F(numerator, 4)
        a, ell = primitive({q:G(1)})
        finite_primitive = not ell and (not a or min(a) > 0)
        check('Power threshold regression', finite_primitive == (q > 1))
    N = 16
    for _ in range(100):
        b = clean({F(k):G(rng.randrange(-3, 4)) for k in range(2, 7)})
        theta, ell = primitive(b)
        check('Positive-phase primitive', not ell and (not theta or min(theta) > 0))
        h = scale(theta, I)
        y = exp_jet(h, N)
        residual = add(derivative(y), scale(mul(b, y), -I))
        check('Oscillatory small-phase equation jet', not jet(residual, N))
        check('Unit-circle exponential jet', mul(y, exp_jet(scale(h, -1), N), N) == ONE)
    # Cayley coordinate (1+it)/(1-it), normalized derivative -2it^2/(1+t^2).
    inverse = {F(k): I**k for k in range(N+1)}
    y = mul({F(0):G(1), F(1):I}, inverse, N)
    coefficient = {F(2+2*k): -2*I*((-1)**k) for k in range(N//2)}
    check('Cayley logarithmic derivative jet', not jet(add(derivative(y), scale(mul(coefficient,y),-1)), N))
    for degree in range(9):
        f = {F(-k):G(k+1, 2-k) for k in range(degree+1)}
        for lam in (I, G(1, 1), G(2), G(-3, 2)):
            # Finite inverse on polynomials in omega: -(D^k f)/lambda^(k+1).
            y, term, k = {}, f, 0
            while term:
                y = add(y, scale(term, -G(1)/(lam**(k+1))))
                term, k = derivative(term), k+1
            check('Polynomial forcing exact inverse', add(derivative(y), scale(y,-lam)) == f)
        term = f
        for _ in range(degree+1):
            term = derivative(term)
        check('Repeated real-root amplitude', not term)
    return {
        'status':'passed', 'seed':20260921, 'python_version':platform.python_version(),
        'checks':sum(counts.values()), 'categories':counts,
        'series_cutoff':N,
        'scope':'Exact finite Gaussian-rational Laurent algebra and truncated formal series only.',
        'not_verified':['Infinite Hahn summability', 'The Berarducci-Mantova construction',
                        'Proper-class statements', 'General theorems in the article',
                        'Novelty or literature priority', 'Any Lean formalization']
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1]/'data'/'verification.json')
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
