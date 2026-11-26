#!/usr/bin/env python3
"""Exact finite certificates for the A5 one-sided prime-sum target.

Only the Python standard library is used.  This checks finite algebra, not the
unproved analytic estimate required by the transfer theorem.  Run as
    python3 a5_detector.py > a5_detector_results.json
"""
import itertools
import json
import math
from fractions import Fraction

N = 5
ID = tuple(range(N))


def mul(g, h):
    return tuple(g[h[i]] for i in range(N))


def inv(g):
    return tuple(g.index(i) for i in range(N))


def power(g, k):
    out = ID
    for _ in range(k):
        out = mul(out, g)
    return out


def even(g):
    return sum(g[i] > g[j] for i in range(N) for j in range(i + 1, N)) % 2 == 0


def order(g):
    return next(k for k in range(1, 61) if power(g, k) == ID)


G = set(filter(even, itertools.permutations(range(N))))
rotation = (1, 2, 3, 4, 0)
H12 = {power(rotation, k) for k in range(5)}
H5 = {g for g in G if g[0] == 0}
H6 = {g for g in G if {mul(mul(g, h), inv(g)) for h in H12} == H12}
assert (len(G), len(H5), len(H6), len(H12)) == (60, 12, 10, 5)


def perm_char(g, subgroup):
    numerator = sum(mul(mul(inv(x), g), x) in subgroup for x in G)
    assert numerator % len(subgroup) == 0
    return numerator // len(subgroup)


def chars(g):
    return [perm_char(g, H) for H in (H5, H6, H12)]


def weight(g):
    return sum(chars(g)) - 2


classes = []
left = set(G)
while left:
    g = min(left)
    cls = {mul(mul(x, g), inv(x)) for x in G}
    classes.append(cls)
    left -= cls
classes.sort(key=lambda c: (order(next(iter(c))), min(c)))
labels = ["1A", "2A", "3A", "5A", "5B"]
table = []
for label, cls in zip(labels, classes):
    g = min(cls)
    p5, p6, p12 = chars(g)
    assert all(chars(h) == [p5, p6, p12] for h in cls)
    table.append({"class": label, "size": len(cls), "order": order(g),
                  "representative_zero_based": list(g),
                  "pi5": p5, "pi6": p6, "pi12": p12, "W": weight(g)})

for g in G:
    p5, p6, p12 = chars(g)
    assert 4 * p5 + 2 * p6 + 3 * p12 - 8 == (60 if g == ID else 0)
    assert weight(g) >= 0
    for k in range(1, order(g) + 1):
        assert weight(power(g, k)) >= 0

weights = [weight(g) for g in G]
mean = Fraction(sum(weights), len(G))
variance = sum((Fraction(w) - mean) ** 2 for w in weights) / len(G)
assert mean == 1 and variance == 7 and max(weights) == 21


def trim(poly):
    out = list(poly)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def remainder(poly, divisor, p):
    out = trim([c % p for c in poly])
    divisor = trim([c % p for c in divisor])
    while len(out) >= len(divisor) and out != [0]:
        j = len(out) - len(divisor)
        c = out[-1] * pow(divisor[-1], -1, p) % p
        for i, a in enumerate(divisor):
            out[i + j] = (out[i + j] - c * a) % p
        out = trim(out)
    return out


def multiply(a, b, p):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % p
    return trim(out)


def eval_poly(poly, a, p):
    return sum(c * pow(a, i, p) for i, c in enumerate(poly)) % p


def determinant(matrix):
    """Exact Gaussian elimination over Q; size here is only nine."""
    a = [list(map(Fraction, row)) for row in matrix]
    result = Fraction(1)
    for j in range(len(a)):
        k = next((k for k in range(j, len(a)) if a[k][j]), None)
        if k is None:
            return Fraction(0)
        if k != j:
            a[j], a[k] = a[k], a[j]
            result = -result
        pivot = a[j][j]
        result *= pivot
        for k in range(j + 1, len(a)):
            ratio = a[k][j] / pivot
            for t in range(j, len(a)):
                a[k][t] -= ratio * a[j][t]
    return result


def resultant(f, h):
    f, h = list(reversed(f)), list(reversed(h))
    m, n = len(f) - 1, len(h) - 1
    rows = [[0] * j + f + [0] * (n - j - 1) for j in range(n)]
    rows += [[0] * j + h + [0] * (m - j - 1) for j in range(m)]
    return determinant(rows)


f = [16, 20, 0, 0, 0, 1]  # ascending coefficients of x^5 + 20x + 16
derivative = [i * f[i] for i in range(1, len(f))]
disc = (-1) ** (5 * 4 // 2) * resultant(f, derivative)
assert disc.denominator == 1 and disc == 32000 ** 2
quadratics_mod3 = [[1, 0, 1], [2, 1, 1], [2, 2, 1]]
assert all(eval_poly(f, a, 3) for a in range(3))
assert all(remainder(f, q, 3) != [0] for q in quadratics_mod3)
# A reducible quintic has a linear or quadratic factor; these are all the
# monic irreducible quadratics over F_3, so f is irreducible modulo 3.
cubic_mod7 = [-2, -2, 2, 1]
assert all(eval_poly(cubic_mod7, a, 7) for a in range(7))
assert multiply(multiply([2, 1], [3, 1], 7), cubic_mod7, 7) == [c % 7 for c in f]

# The symbolic optimum is elementary: for a,b,c >= 1, the identity-class
# coefficient of a*pi5+b*pi6+c*pi12+(1-a-b-c)*1 is 1+4a+5b+11c >= 21.
# The table checks that equality a=b=c=1 is feasible on every class.
result = {
    "purpose": "Exact algebraic certificate; no analytic prime-sum estimate is claimed",
    "group_order": len(G),
    "subgroup_orders": {"A4": len(H5), "D5": len(H6), "C5": len(H12)},
    "class_table": table,
    "regular_character_identity": "reg = 4*pi5 + 2*pi6 + 3*pi12 - 8*1",
    "positive_detector_identity": "W = pi5 + pi6 + pi12 - 2*1",
    "mean": str(mean), "variance": str(variance),
    "minimum_weight": min(weights), "maximum_weight": max(weights),
    "prime_power_positivity_checked": True,
    "polynomial": "x^5 + 20*x + 16",
    "polynomial_discriminant": int(disc),
    "polynomial_discriminant_square_root": math.isqrt(int(disc)),
    "mod3_linear_evaluations": [eval_poly(f, a, 3) for a in range(3)],
    "mod3_quadratic_remainders_ascending": [remainder(f, q, 3) for q in quadratics_mod3],
    "mod7_factorization": "(x+2)*(x+3)*(x^3+2*x^2-2*x-2)",
    "mod7_cubic_evaluations": [eval_poly(cubic_mod7, a, 7) for a in range(7)],
    "galois_group_certificate": "square discriminant; irreducible mod 3; mod 7 cycle type 1+1+3; excludes orders 15 and 30 inside A5",
    "scoped_peak_optimum": {"normalization": "mean 1; a,b,c >= 1 in the three selected Dedekind factors", "value": 21, "attained_at": [1, 1, 1]},
}
print(json.dumps(result, indent=2))
