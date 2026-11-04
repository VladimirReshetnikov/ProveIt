#!/usr/bin/env python3
"""Finite diagnostics for a scalar limitation, not a full graph witness."""
import sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")


def y_ordinate(index, base):
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, base * current - previous
    return previous


def small_sample():
    bits, n = 30, 16
    q = 1 << bits
    beta, j, h = q - 1, 1, q - 1
    y, t, r = q**3, 2 * q**3, 2 * n - 1
    x = 1 << r
    assert q == beta * j + 1 and x % q == 0 and y % q**3 == 0
    assert n < r < 2 * n and r % 2 == 1
    assert 2 * (n - 1)**2 > 3 * bits + 2

    y_first = y_ordinate(n, x * t**2 + 2)
    k = 2 * y_first
    c = y_ordinate(r, t * (x + 1) + 2)
    assert t * y_first < c
    assert c > 2 * t * y_first >= k * (y + 1)
    eta = c - k * y
    zeta = k - eta
    assert eta > k and zeta < 0
    divisor = 4 * y * (x + 1) - 1
    assert h * x * (x - (1 << r)) * ((1 << r) * x + 1) % divisor == 0

    mc, mf, k0 = 28, 0, 1
    rank_tail = mc + q * mf
    target = 2 * n - 1
    modulus = q**4
    g0 = (-(1 + q**2) * (target - rank_tail)) % modulus
    g = g0 - modulus
    f, c_port = 1, q * (q - 1) - g
    rank = (q**2 - 1) * g + rank_tail
    assert g < 0 and f > 0 and c_port > 0 and f + c_port >= q
    assert q * (q - f) - c_port == g
    assert (k0 + 1) * c_port - f >= 0
    assert rank % modulus == target % modulus
    assert k % modulus == (2 * n) % modulus
    assert (rank + 1 - 2 * n) % modulus == 0
    assert (k - rank - 1) % modulus == 0
    assert (c_port + mc + q * (f + mf) + 1 - 2 * n) % q**2 == 0
    print(f"exact sample: B={bits}, n={n}, r={r}, k_bits={k.bit_length()}, c_bits={c.bit_length()}")
    print("PASS: gap, zero projection, rank residues, guard failure, negative zeta")


def symbolic_exponents():
    bits = 67 * 8807
    n = 295035
    r = 2 * n - 1
    assert bits == 590069 and r >= bits and n >= 5
    assert 2 * (n - 1)**2 > 3 * bits + 2
    print(f"symbolic exponents: B={bits}, n={n}, r={r}")
    print("PASS: index, q-divisibility exponent and growth inequalities only")


small_sample()
symbolic_exponents()
