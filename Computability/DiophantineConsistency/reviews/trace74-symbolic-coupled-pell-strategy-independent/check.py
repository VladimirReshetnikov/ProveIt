#!/usr/bin/env python3
"""Independent arithmetic diagnostics; not an evaluation of the huge graph."""
import sys
from math import gcd

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")


def pell(z, index):
    delta = z * z - 1
    x, y = 1, 0
    for _ in range(index):
        x, y = z * x + delta * y, x + z * y
    return x, y


def odd_quotient_mod(s, j, modulus):
    factor = (4 * s * s - 2) % modulus
    x, y = 1, (factor - 1) % modulus
    for _ in range(j):
        x, y = y, (factor * y - x) % modulus
    return x % modulus


# Independent sign diagnostic: unlike the author's r=3 example, this has
# r=1 mod 4 and odd s, as in the symbolic construction. We choose a t
# directly satisfying the required divisibilities; this is not the full graph.
z, r, c, t = 2, 5, 209, 1045
delta = z * z - 1
assert pell(z, r)[1] == c and r % 4 == 1 and t % c == 0
phi, yt = pell(z, t)
f, ordinate2t = pell(z, 2 * t)
assert yt % (c * c) == 0 and f == 2 * phi * phi - 1
assert f % c == 1 and gcd(f, c) == 1
S = delta * ordinate2t
assert S % c == 0 and S * S + z * z - 1 == delta * f * f
u = r + 4 * t
assert u % 4 == 1
V = odd_quotient_mod(S, (u - 1) // 2, f * c)
assert V % f == (-c) % f and V % c == r % c
rank = -r
assert (V + c + f * rank) % (f * c) == 0
print("r=5 odd-shift toy: both Chebyshev congruences and CRT PASS")

# A sparse-polynomial identity for the final 74 output in abstract
# register variables Q,Z,M,E,F,V. This does not parse the row source.
def add(a, b, sign=1):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, 0) + sign * value
        if out[key] == 0:
            del out[key]
    return out


def mul(a, b):
    out = {}
    for left, lv in a.items():
        for right, rv in b.items():
            key = tuple(x + y for x, y in zip(left, right))
            out[key] = out.get(key, 0) + lv * rv
    return {key: value for key, value in out.items() if value}


one = {(0, 0, 0, 0, 0, 0): 1}
variables = [{tuple(int(i == j) for i in range(6)): 1} for j in range(6)]
Q, Z, M, E, F0, graph_v = variables
zz = mul(Z, Z)
g = mul(mul(mul(M, M), E), F0)
v2 = mul(graph_v, graph_v)
row_output = add(mul(Q, add(zz, mul(g, v2), -1)), add(g, zz, -1))
factored = add(mul(add(Q, one, -1), zz), mul(g, add(mul(Q, v2), one, -1)), -1)
assert row_output == factored
print("abstract 74 output expansion PASS; no symbolic full graph evaluated")
