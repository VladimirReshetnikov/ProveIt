#!/usr/bin/env python3
"""Exact modular toy of the coupled Pell/Chebyshev congruence.

This is an abstract finite instance, not a trace74 zero or proof of the
symbolic instance. No enormous auxiliary Pell values are materialized.
"""
import sys
from math import gcd

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit("use python3 -I -S -B without optimization")


def mul_unit(a, b, delta):
    x, y = a
    u, v = b
    return x * u + delta * y * v, x * v + y * u


def unit_power(lam, delta, exponent):
    acc = (1, 0)
    base = (lam, 1)
    while exponent:
        if exponent & 1:
            acc = mul_unit(acc, base, delta)
        base = mul_unit(base, base, delta)
        exponent >>= 1
    return acc


def mat_mul(a, b, modulus):
    return tuple(
        (a[2 * i] * b[j] + a[2 * i + 1] * b[2 + j]) % modulus
        for i in range(2) for j in range(2)
    )


def mat_power(matrix, exponent, modulus):
    acc = (1, 0, 0, 1)
    while exponent:
        if exponent & 1:
            acc = mat_mul(acc, matrix, modulus)
        matrix = mat_mul(matrix, matrix, modulus)
        exponent >>= 1
    return acc


def aux_V_mod(S, h, modulus):
    if h == 0:
        return 1 % modulus
    Q = (S * S) % modulus
    V1 = (4 * Q - 3) % modulus
    matrix = ((4 * Q - 2) % modulus, modulus - 1, 1, 0)
    powered = mat_power(matrix, h - 1, modulus)
    return (powered[0] * V1 + powered[1]) % modulus


lam, delta, r, tau = 2, 3, 5, 1
xr, c = unit_power(lam, delta, r)
assert c == 209 and r % 4 == 1 and xr * xr - delta * c * c == 1
u = r * c
froot, yu = unit_power(lam, delta, u)
assert yu % (c * c * tau) == 0
i = yu // (c * c * tau)
U = i * c * c
a = delta * U * U * tau * tau
assert froot * froot == 1 + a
F = 1 + 2 * a
j = 2 * u
I = 2 * yu * froot
assert F * F - delta * I * I == 1 and I % (c * c) == 0
assert j % c == 0 and j % 2 == 0 and F % c == 1 and gcd(F, c) == 1
S = delta * I
Q = delta * 4 * a * (1 + a)
assert Q == S * S

s = r + 2 * j
h = (s - 1) // 2
assert s % 2 == 1 and h % 2 == 0
modulus = F * c
V = aux_V_mod(S, h, modulus)
assert V % F == (-c) % F
assert V % c == r % c
R = -r
assert (V + c + F * R) % modulus == 0
print(f"abstract toy: r={r}, c={c}, u={u}, j={j}, h={h}; congruences PASS")
print("V is checked modulo F*c; positivity of the eventual T and graph zero are not computed.")
