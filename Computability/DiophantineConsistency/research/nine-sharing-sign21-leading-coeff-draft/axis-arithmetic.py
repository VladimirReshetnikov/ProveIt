#!/usr/bin/env python3
"""Check hand-transcribed septic axis arithmetic, not Lean or file binding."""
def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c
t = [0, 1]
q = mul([1, 1], mul(t, [2, 1]))
row = [-v for v in mul(mul(q, q), t)]
assert row == [0, 0, 0, -4, -12, -13, -6, -1]
assert mul(row, row)[14] == 1
print('PASS hand-transcribed axis arithmetic; no Lean or external binding claim')
