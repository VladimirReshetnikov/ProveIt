#!/usr/bin/env python3
"""Exact small Pell norm checks; never asserts a full graph zero."""
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")


def ordinate_pair(index, z):
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, z * current - previous
    return previous, current


bits, n, r = 7, 63, 77
q = 1 << bits
y = q**3
t = 2 * y
x = 1 << r
p = x * y * y
assert x % q == 0 and n < r < 2 * n and r % 2 == 1
assert r * (r - n) == (3 * bits + 1) * (2 * n - r)

first_z = 4 * p + 2
first, first_next = ordinate_pair(n, first_z)
k = 2 * first
tau = first_next - (first_z // 2) * first
assert tau > 0
assert first_next**2 - first_z * first_next * first + first**2 == 1
assert tau**2 == 1 + p * (p + 1) * k**2
actual_e = 1 + (x * y) * (k * y) * ((x * y) * (k * y) + k)
assert tau**2 == actual_e

a = y * (x + 1)
main_z = 2 * (a + 1)
c, main_next = ordinate_pair(r, main_z)
main_x = main_next - (main_z // 2) * c
assert main_x > 0
assert main_next**2 - main_z * main_next * c + c**2 == 1
assert main_x**2 == 1 + a * (a + 2) * c**2
eta, zeta = c - k * y, k - (c - k * y)
assert eta > 0 and zeta > 0 and c == k * y + eta and k == eta + zeta

mc, mf, k0 = 2, q, 1
q4 = q**4
rank_tail = mc + q * mf
g0 = (-(1 + q**2) * (2 * n - 1 - rank_tail)) % q4
g = g0 - q4
f, c_port = 1, q * (q - 1) - g
rank = (q**2 - 1) * g + rank_tail
valuation = (1, f, c_port, 1, 1, x // q, 1, 1, eta, zeta)
assert all(value > 0 for value in valuation)
assert (k - rank - 1) % q4 == 0 and f + c_port >= q
assert (k0 + valuation[3]) * c_port - f >= 0
print(f"B={bits}, n={n}, r={r}: both norms and positive split PASS")

B = 67 * 8807
s = 3 * B + 1
d = s - 2048
R = 55319**2 - 2 * s
N = R - d
assert B == 590069 and R == 3056651345 and N == 3054883185
assert R * d == s * (2 * N - R) and R >= B
assert R - (s - 1) >= (4 * (R - 1)).bit_length()
print("symbolic case: exponent and size bookkeeping PASS")
print("No full graph zero or Lean theorem is asserted.")
