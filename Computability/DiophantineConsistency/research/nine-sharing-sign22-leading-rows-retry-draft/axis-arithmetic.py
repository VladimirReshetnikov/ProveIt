#!/usr/bin/env python3
"""Independent integer-coefficient arithmetic check of the stated axis formulas.

This checks the hand-transcribed row algebra, not Lean/JSON correspondence.
Coefficients are represented in ascending order.
"""
def add(a, b):
    return [sum(z) for z in zip(a + [0] * max(0, len(b) - len(a)),
                                b + [0] * max(0, len(a) - len(b)))]
def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c
def neg(a):
    return [-x for x in a]
t, one = [0, 1], [1]
u = mul(add(add(t, one), add(t, one)), t)
a = add(u, add(t, one))
x = add(t, t)
delta = add(add(mul(x, x), mul([4], x)), [3])
dc2 = neg(mul(delta, mul(a, a)))
v = mul(t, u)
n0 = add(neg(mul(v, add(v, add(add(t, one), add(t, one))))), [-1])
assert dc2 == [-3, -26, -91, -164, -160, -80, -16]
assert n0 == [-1, 0, -4, -8, -8, -8, -4]
assert dc2[6] ** 2 + n0[6] ** 2 == 272
print('PASS hand-transcribed axis arithmetic; no Lean or external binding claim')
