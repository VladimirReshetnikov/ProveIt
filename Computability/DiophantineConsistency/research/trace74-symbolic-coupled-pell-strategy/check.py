#!/usr/bin/env python3
"""Finite diagnostics for the proposed coupled-Pell construction.

Not a full graph-zero check, Lean theorem, or proof of the symbolic instance.
"""
import math
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")

def xy(z, index):
    delta = z*z-1
    x, y = 1, 0
    for _ in range(index):
        x, y = z*x+delta*y, x+z*y
    return x, y

def odd_quotient_mod(S, j, modulus):
    # T_(2j+1)(S)/S: recurrence P_(j+2)=(4S²−2)P_(j+1)−P_j.
    coefficient = (4*S*S-2) % modulus
    a, b = 1, (coefficient-1) % modulus
    for _ in range(j):
        a, b = b, (coefficient*b-a) % modulus
    return a % modulus

# Nontrivial c and nontrivial f; this tests the odd-r sign convention.
z, r, t0 = 2, 3, 45
delta = z*z-1
_, c = xy(z, r)
assert c == 15 and xy(z, t0)[1] % (c*c) == 0
t = c*t0
phi, yt = xy(z, t)
assert yt % (c*c) == 0 and t % c == 0
f, I = xy(z, 2*t)
assert f == 2*phi*phi-1 and I == 2*phi*yt
S = delta*I
assert S*S+z*z-1 == delta*f*f
assert f % c == 1 and math.gcd(f, c) == 1
steps = 2  # even because (r−1)/2 is odd
u = r+4*t*steps
j = (u-1)//2
assert u % 4 == 3
Vmod = odd_quotient_mod(S, j, f*c)
a, b = 0, 1
for _ in range(u):
    a, b = b, (2*z*b-a) % f
yr_mod_f = a
assert yr_mod_f == c % f  # even number of 4t shifts
assert Vmod % f == (-c) % f
assert Vmod % c == (-r) % c
R = -12  # R ≡ +r mod c, matching this toy's r ≡ 3 mod 4.
assert (Vmod+c+f*R) % (f*c) == 0
print("small odd-Pell congruence and CRT compatibility PASS")
print("No full graph zero or Lean theorem is asserted.")
