#!/usr/bin/env python3
"""Finite exponent checks and a small analogous scalar instance only."""
import sys
from math import gcd

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")


def ordinate(index, coefficient):
    old, cur = 0, 1
    for _ in range(index):
        old, cur = cur, coefficient * cur - old
    return old


B = 67 * 8807
s = 3 * B + 1
assert (B, s) == (590069, 1770208)
assert s == 32 * 55319
g = 2048
d = s - g
r = 55319**2 - 2 * s
n = r - d
assert (d, r, n) == (1768160, 3056651345, 3054883185)
assert r % 2 == 1 and n < r < 2 * n and r >= B
assert r * d == s * (2 * n - r)
# 4(r-1)Y < 2^r, Y=2^(s-1), checked using bit lengths only.
assert r - (s - 1) >= (4 * (r - 1)).bit_length()
print("symbolic beta: exact index identity and size comparison PASS")

# The same power-matching construction for B=1: s=4=4*1,
# g=8 is not below s; search a modest analogous even s instead.
small = None
for b in range(2, 12):
    s0 = 3 * b + 1
    if s0 % 2:
        continue
    a = 0
    u = s0
    while u % 2 == 0:
        a += 1
        u //= 2
    g0 = 2 ** (2 * a + 1)
    rr = u * u - 2 * s0
    dd = s0 - g0
    nn = rr - dd
    if dd > 0 and nn >= 2 and rr % 2 == 1 and nn < rr < 2 * nn and rr >= b:
        if rr - (s0 - 1) >= (4 * (rr - 1)).bit_length():
            small = b, s0, nn, rr
            break
assert small is not None
b, s0, nn, rr = small
assert rr < 10000  # keep the diagnostic finite and intentionally small
q = 2**b
Y = q**3
t = 2 * Y
X = 2**rr
P = X * t * t
k = 2 * ordinate(nn, P + 2)
c = ordinate(rr, t * (X + 1) + 2)
eta = c - k * Y
zeta = k - eta
assert eta > 0 and zeta > 0 and k == eta + zeta
assert k * Y < c < k * (Y + 1)
assert X % q == 0 and (rr * (rr - nn) == s0 * (2 * nn - rr))
assert k % (q**4) == (2 * nn) % (q**4)
assert (q - 1) * X * (X - 2**rr) * (2**rr * X + 1) == 0
MC, MF, K0, w = 2, q, 1, X // q
assert w > 0 and w * q == X
RJ = MC + q * MF
Rtarget = 2 * nn - 1
assert c % 2 == 1 and gcd(c, q * q - 1) == 1
Gq = (-(1 + q * q) * (Rtarget - RJ)) % (q**4)
Gc = ((rr - RJ) * pow(q * q - 1, -1, c)) % c
adjust = ((Gc - Gq) * pow(q**4, -1, c)) % c
G0 = Gq + q**4 * adjust
G = G0 - (q**4) * c * (RJ + q**4 + 2)
F, C = 1, q * (q - 1) - G
R = (q * q - 1) * G + RJ
assert G < 0 and C > 0 and G == q * (q - F) - C
assert (k - R - 1) % (q**4) == 0
assert R < 0 and (abs(R) + rr) % c == 0
assert R + q**3 + q + 1 <= q**4
assert F + C >= q and (K0 + w) * C - F >= 0
print(f"small analogous B={b}, n={nn}, r={rr}: interval, CRT and scalar checks PASS")
print("No full graph zero or Lean theorem is asserted.")
