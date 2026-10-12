#!/usr/bin/env python3
"""High-precision diagnostics for the two-tail and Stieltjes generators.

These checks are deliberately independent of the exact determinant certificate.
They detect sign, indexing, and anchoring mistakes in the analytic formulas but
are not used as proof gates.
"""
from __future__ import annotations

import mpmath as mp

mp.mp.dps = 80
TOL = mp.mpf("1e-60")


def sum_until(term, start: int = 0, cutoff: mp.mpf = mp.mpf("1e-75"), max_terms: int = 20000):
    total = mp.mpf("0")
    small = 0
    for n in range(start, max_terms):
        value = term(n)
        total += value
        if abs(value) < cutoff:
            small += 1
            if small >= 8:
                return total
        else:
            small = 0
    raise RuntimeError("series did not reach the requested cutoff")


def li_depth2(r, s, z):
    # Li_{r,s}(1,z) = sum_{m>n>=1} z^n/(m^r n^s)
    return sum_until(lambda n: z**n * mp.zeta(r, n + 1) / (mp.mpf(n) ** s), start=1)


def check(label: str, lhs, rhs):
    err = abs(lhs - rhs)
    print(f"{label}: {mp.nstr(err, 8)}")
    if err > TOL:
        raise SystemExit(f"{label} failed: error={mp.nstr(err, 30)}")


# Two-tail polylogarithmic generator.
p, q, z = 3, 4, mp.mpf("0.37")
lhs = sum_until(lambda n: mp.zeta(p, n + 1) * mp.zeta(q, n + 1) * z**n)
rhs = (
    mp.zeta(p) * mp.zeta(q)
    - li_depth2(p, q, z)
    - li_depth2(q, p, z)
    - mp.polylog(p + q, z)
) / (1 - z)
check("two-tail generator", lhs, rhs)


# Parameter-level Stieltjes correlation identity, safely inside Re(alpha),Re(beta)>0.
a, b, z = mp.mpf("0.23"), mp.mpf("0.31"), mp.mpf("0.29")
lhs = sum_until(
    lambda n: (mp.zeta(1 + a, n + 1) - 1 / a)
    * (mp.zeta(1 + b, n + 1) - 1 / b)
    * z**n
)
G_a = mp.zeta(1 + a) - 1 / a
G_b = mp.zeta(1 + b) - 1 / b
K = (
    li_depth2(1 + a, 1 + b, z)
    - mp.polylog(1 + b, z) / a
    + li_depth2(1 + b, 1 + a, z)
    - mp.polylog(1 + a, z) / b
    + mp.polylog(2 + a + b, z)
)
rhs = (G_a * G_b - K) / (1 - z)
check("parameter Stieltjes kernel", lhs, rhs)


# Lowest coefficient: digamma square.
z = mp.mpf("0.41")
lhs = sum_until(lambda n: (mp.euler - mp.harmonic(n)) ** 2 * z**n)
rhs = ((mp.euler + mp.log(1 - z)) ** 2 + mp.polylog(2, z)) / (1 - z)
check("digamma-square generator", lhs, rhs)


# Anchored primitive at z=1/2.
lhs = sum_until(
    lambda n: (mp.euler - mp.harmonic(n)) ** 2
    / ((n + 1) * mp.mpf(2) ** (n + 1))
)
log2 = mp.log(2)
rhs = (
    (mp.euler**3 - (mp.euler - log2) ** 3) / 3
    + mp.pi**2 * log2 / 12
    - log2**3 / 6
    - mp.zeta(3) / 4
)
check("anchored half-value", lhs, rhs)

print("PASS: all analytic generator diagnostics")
