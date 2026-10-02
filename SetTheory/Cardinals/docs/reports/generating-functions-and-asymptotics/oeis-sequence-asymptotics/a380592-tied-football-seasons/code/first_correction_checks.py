#!/usr/bin/env python3
"""Compute the first local correction by independent recursive partitions.

The finite algebra complements the report's analytic remainder argument.
"""
import sympy as S
from functools import lru_cache
from collections import Counter
from fractions import Fraction as F
import json
from output_support import write_result
n, x, y = S.symbols('n x y')
I = S.I
mu = S.Rational(4, 3) * (x + y)
v = [3 * x - mu, x + y - mu, 3 * y - mu]
m = {0: S.Integer(1), 1: S.Integer(0)}
k = {1: S.Integer(0)}
for r in range(2, 7):
    m[r] = S.expand(sum((z ** r / 3 for z in v)))
    k[r] = S.expand(m[r] - sum((S.binomial(r - 1, j - 1) * k[j] * m[r - j] for j in range(1, r))))
P = S.symbols('P0:7')
L = {}
for r in range(3, 7):
    c = [k[r].coeff(x, a).coeff(y, r - a) for a in range(r + 1)]
    L[r] = S.expand(I ** r / S.factorial(r) * (sum((c[a] * P[a] * P[r - a] for a in range(r + 1))) - sum(c) * P[r])).subs(P[0], n).expand()

@lru_cache(None)
def grouped_partitions(degrees):
    """Counts set partitions grouped by the sorted sums of degrees in blocks."""
    ans = Counter()
    blocks = []

    def rec(j):
        if j == len(degrees):
            ans[tuple(sorted(blocks))] += 1
            return
        d = degrees[j]
        for z in range(len(blocks)):
            blocks[z] += d
            rec(j + 1)
            blocks[z] -= d
        blocks.append(d)
        rec(j + 1)
        blocks.pop()
    rec(0)
    return tuple(ans.items())

def df(k):
    if k <= 0:
        return 1
    return int(S.factorial2(k))

@lru_cache(None)
def distinct_moment(ds):
    """Recursive Wick expansion for distinct coordinates with covariance a I+b J."""
    if sum(ds) % 2:
        return ()
    D = sum(ds)
    out = Counter()

    def rec(j, K, c):
        if j == len(ds):
            B = D // 2 - K
            out[K, B] += c * df(2 * B - 1)
            return
        d = ds[j]
        for h in range(d // 2 + 1):
            rec(j + 1, K + h, c * int(S.binomial(d, 2 * h)) * df(2 * h - 1))
    rec(0, 0, 1)
    return tuple(out.items())

@lru_cache(None)
def moment(degrees, u):
    """Constant and 1/n terms, rejecting a positive leading power of n."""
    ans = Counter()
    for ds, multiplicity in grouped_partitions(degrees):
        l = len(ds)
        for (K, B), c in distinct_moment(ds):
            e = u + l - K - 2 * B
            if e < -1:
                continue
            lead = F(multiplicity * c) * F(9, 28) ** K * F(117, 28) ** B
            ans[e] += lead
            if e >= 0:
                ans[e - 1] += lead * (-F(l * (l - 1), 2) + F(K, 14) + F(15 * B, 14))
            if e > 0:
                raise RuntimeError(('Need more expansion terms', degrees, u, e))
    return tuple(ans.items())

def E(poly):
    """Apply the exact power-sum moment rule to every polynomial monomial."""
    out = Counter()
    poly = S.Poly(S.expand(poly), n, *P[1:])
    for powers, coeff in poly.terms():
        u = powers[0]
        degrees = tuple((d for d, t in enumerate(powers[1:], 1) for j in range(t)))
        for e, c in moment(degrees, u):
            out[e] += coeff * S.Rational(c.numerator, c.denominator)
    return tuple((S.simplify(out.get(e, 0)) for e in (0, -1)))

def add(*xs):
    return tuple((S.simplify(sum((x[j] for x in xs))) for j in (0, 1)))

def mul(a, b):
    return (a[0] * b[0], a[0] * b[1] + a[1] * b[0])

def sc(a, c):
    return tuple((S.simplify(z * c) for z in a))
means = {name: E(poly) for name, poly in {'L4': L[4], 'L6': L[6], 'L3sq': L[3] ** 2, 'L3L5': L[3] * L[5], 'L4sq': L[4] ** 2, 'L3sqL4': L[3] ** 2 * L[4], 'L3four': L[3] ** 4}.items()}
var4 = add(means['L4sq'], sc(mul(means['L4'], means['L4']), -1))
k334 = add(means['L3sqL4'], sc(mul(means['L3sq'], means['L4']), -1))
k3333 = add(means['L3four'], sc(mul(means['L3sq'], means['L3sq']), -3))
ans = add(means['L4'], sc(means['L3sq'], S.Rational(1, 2)), means['L6'], means['L3L5'], sc(var4, S.Rational(1, 2)), sc(k334, S.Rational(1, 2)), sc(k3333, S.Rational(1, 24)))
assert ans == (-S.Rational(7865, 32928), S.Rational(1147975, 45177216))
out = {'scope': 'Exact local Gaussian coefficient calculation; analytic remainder bounds are treated separately', 'L': {str(r): str(v) for r, v in L.items()}, 'moments_constant_and_1_over_n': {r: [str(v) for v in t] for r, t in means.items()}, 'variance_L4': [str(v) for v in var4], 'cumulant_L3_L3_L4': [str(v) for v in k334], 'cumulant_L3_four': [str(v) for v in k3333], 'log_local_integral': [str(v) for v in ans]}
write_result('first_correction_checks', out)
print(json.dumps(out, indent=2))
