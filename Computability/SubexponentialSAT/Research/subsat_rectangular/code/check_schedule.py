#!/usr/bin/env python3
"""Exact certificate for the r=(8,10,6,4,...) rectangular-MM schedule.
Python standard library only; it verifies arithmetic, not the imported algorithms.
"""
from fractions import Fraction as F
from math import isqrt
import json

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)
SCALE = 10 ** 14

def sqrti(x):
    x = F(x)
    n = isqrt(x.numerator * SCALE * SCALE // x.denominator)
    lo, hi = (F(n, SCALE), F(n + 1, SCALE))
    require(lo * lo <= x <= hi * hi, 'certificate condition failed')
    return (lo, hi)

def atani(x, n=64):
    s = sum(((-1) ** j * x ** (2 * j + 1) / F(2 * j + 1) for j in range(n)), F())
    t = (-1) ** n * x ** (2 * n + 1) / F(2 * n + 1)
    return (min(s, s + t), max(s, s + t))
p5, p239 = (atani(F(1, 5)), atani(F(1, 239)))
pi = (16 * p5[0] - 4 * p239[1], 16 * p5[1] - 4 * p239[0])
x = F(1, 3)
n = 64
l = sum((2 * x ** (2 * j + 1) / F(2 * j + 1) for j in range(n)), F())
ln2 = (l, l + 2 * x ** (2 * n + 1) / F(2 * n + 1) / (1 - x * x))
sqrt2 = sqrti(2)
kappa = (pi[0] * sqrt2[0] / ln2[1], pi[1] * sqrt2[1] / ln2[0])

def add(a, b):
    return (a[0] + b[0], a[1] + b[1])

def mul(a, b):
    return (a[0] * b[0], a[1] * b[1])

def div(a, b):
    return (a[0] / b[1], a[1] / b[0])

def point(x):
    return (F(x), F(x))

def minus1(a):
    return (1 - a[1], 1 - a[0])

def enc(a):
    return {'lower': str(a[0]), 'upper': str(a[1]), 'decimal_lower': float(a[0]), 'decimal_upper': float(a[1])}
eps = F(1, 100000)
floor_factor = 1 + eps / 2
mid = F(47, 56) + eps
low = F(15, 28)

def cardinal_cost(v):
    v = sorted(v, reverse=True)
    return max(floor_factor ** 2 * (v[0] + v[1]), v[0] + mid ** 2 * v[1] + low ** 2 * v[2])

def ledger(r, blocks):
    ops = []

    def build(k):
        if k == 1:
            return
        a = k // 2
        b = k - a
        build(a)
        build(b)
        v = [2 * a * (r - k), 2 * a * b, 2 * b * (r - k)]
        ops.append({'operation': f'merge {a}+{b}', 'classes': v, 'squared_cost': str(cardinal_cost(v))})
    for k in blocks:
        build(k)
    a, b, c = blocks
    v = [2 * a * b, 2 * a * c, 2 * b * c]
    ops.append({'operation': 'triangle', 'classes': v, 'squared_cost': str(cardinal_cost(v))})
    return ops
rs = [8, 10, 6, 4]
blocks = [(3, 3, 2), (4, 3, 3), (2, 2, 2), (2, 1, 1)]
f = [F(49997, 3000000), F(67, 5000), F(17, 2000), F(34003, 8000000)]
m = [F(1), F(1, 4), F(1, 20), F(1, 60)]
card = [30, 48, 16, 8]
ledgers = {}
for r, B, c in zip(rs, blocks, card):
    z = ledger(r, B)
    ledgers[str(r)] = z
    require(max((F(x['squared_cost']) for x in z)) == c * floor_factor ** 2, 'certificate condition failed')
    require(max((2 * k * (r - k) for k in B)) == c, 'certificate condition failed')
A0 = f[0]
A1 = sum(f[:2])
A2 = sum(f[:3])
At = A2 + f[3] / (1 - F(5, 8))
require(At == F(499, 10000), 'certificate condition failed')
require(10 ** 500 < 2 ** 1661, 'certificate condition failed')
require(6 ** 200 < 2 ** 517, 'certificate condition failed')
root_power = F(9, 10) + 6 * A0
row1 = F(9, 10) + F(1661, 500) * A1
row2 = F(9, 10) + F(517, 200) * A2
rowtail = F(9, 10) + 2 * At
require(max(root_power, row1, row2, rowtail) < 1, 'certificate condition failed')
require(max(7 * A0, F(1911, 250) * A1, F(617, 100) * A2, 5 * At) < 1, 'certificate condition failed')
require(F(5, 8) > F(11, 20), 'certificate condition failed')
K = [div(mul(kappa, point(mi)), sqrti(fi)) for mi, fi in zip(m, f)]
a = [div(sqrti(2 * (r - 1)), point(r)) for r in rs]
j = [div(sqrti(c), point(r)) for r, c in zip(rs, card)]
b = [mul(point(floor_factor), ji) for ji in j]
cache = [mul(ai, ki) for ai, ki in zip(a, K)]
local = [mul(bi, ki) for bi, ki in zip(b, K)]
gamma = sqrti(F(2, 5))
tail_factor = div(a[3], minus1(gamma))
require(tail_factor[0] > b[3][1], 'certificate condition failed')
terms = [local[0], add(cache[0], local[1]), add(add(cache[0], cache[1]), local[2]), add(add(add(cache[0], cache[1]), cache[2]), mul(K[3], tail_factor))]
require(all((t[1] < terms[0][0] for t in terms[1:])), 'certificate condition failed')
require(terms[0][1] < 34, 'certificate condition failed')
space = [mul(ji, ki) for ji, ki in zip(j, K)]
require(all((t[1] < space[0][0] for t in space[1:])), 'certificate condition failed')
res = {'status': 'passed', 'scope': 'exact arithmetic certificate; imported contraction and field multiplication are not implemented', 'parameters': {'r': rs, 'f': [str(x) for x in f], 'tail_ratio': '5/8', 'total_capacity': str(At), 'epsilon': str(eps), 'rectangular_floor_factor': str(floor_factor), 'rectangular_middle_weight': str(mid), 'rectangular_small_weight': str(low)}, 'packing_high_degree_exponents': [str(x) for x in (root_power, row1, row2, rowtail)], 'operations': ledgers, 'time_candidates': [enc(x) for x in terms], 'space_candidates': [enc(x) for x in space], 'time_coefficient': enc(terms[0]), 'space_coefficient': enc(space[0])}
print(json.dumps(res, indent=2))
