#!/usr/bin/env python3
"""A fully materialized abstract coupled Pell/carrier algebra diagnostic.

The independent register numbers are not claimed to arise from the 74
graph, its fixed ports, or the symbolic-beta construction.
"""
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")

# Main Pell unit lambda+sqrt(delta), with its r=1 ordinate c=1.
lam, delta, c, r, tau, i = 2, 3, 1, 1, 1, 1
U = i * c * c
E = tau * tau
a = delta * U * U * E
F0 = a + 1
freg = a + F0
phi = 2
assert F0 == phi * phi and freg == 7
I = 2 * U * tau * phi
S = delta * I
Q = delta * 4 * a * F0
assert S == 12 and Q == S * S == 144

# Odd auxiliary index s=5, h=2; these are T_5(S)/S and U_4(S).
V = 16 * S**4 - 20 * S**2 + 5
y = 16 * S**4 - 12 * S**2 + 1
assert (V, y) == (328901, 330049)
assert Q * V * V - (Q - 1) * y * y == 1

# Signed rank R=-1, so actual register shape V=freg(cT-R)-c.
R = -1
numerator = V + c + freg * R
assert numerator % (freg * c) == 0
T = numerator // (freg * c)
assert T == 46985 and T > 0 and freg * (c * T - R) - c == V

# Independent abstract carrier registers: choose h=D=H=B=M=1,
# e=2, Kreg=3, so N0=(hD Kreg-H(DB+h e))/M=0.
h = D = H = Breg = M = 1
e, Kreg = 2, 3
assert M == h * D * H
N0 = (h * D * Kreg - H * (D * Breg + h * e)) // M
assert N0 == 0
v7 = V * V * Breg - N0 + tau * phi * y
assert v7 > 0
Z = h * D * (H * (v7 - V * V * Breg) + Kreg) - H * (D * Breg + h * e)
assert Z == M * tau * phi * y
Gn = E * F0
output = Q * (Z * Z - M * M * Gn * V * V) + (M * M * Gn - Z * Z)
assert output == 0
print("PASS: abstract coupled Pell, integral T, positive carrier and output zero")
print("The independent register values are not asserted to form a 74-graph witness.")
