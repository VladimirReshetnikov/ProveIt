#!/usr/bin/env python3
"""Independent replay of the published order-ten modular certificate.

This verifier deliberately does not import order10_core.py.  It uses
(1) the full Bernoulli recurrence, rather than the even-only recurrence;
(2) a subset-expansion determinant, rather than Gaussian elimination; and
(3) a separately written implementation of the source/retained matrices.
All arithmetic is exact in F_p.
"""
from __future__ import annotations

import json
from hashlib import sha256
from math import comb, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
CERT = json.loads((HERE / "order10_modular_certificate.json").read_text(encoding="utf-8"))
P = int(CERT["prime"])
A = int(CERT["a"])
B0 = int(CERT["b_min"])
B1 = int(CERT["b_max"])
SWITCH = int(CERT["retained_matrix_range"][0])
LIMIT = int(CERT["factorial_table_limit"])


def prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d <= isqrt(n):
        if n % d == 0:
            return False
        d += 2
    return True


assert prime_trial(P)
assert LIMIT < P

fact = [1] * (LIMIT + 1)
for i in range(1, LIMIT + 1):
    fact[i] = fact[i - 1] * i % P
invfact = [1] * (LIMIT + 1)
invfact[LIMIT] = pow(fact[LIMIT], P - 2, P)
for i in range(LIMIT, 0, -1):
    invfact[i - 1] = invfact[i] * i % P


def choose(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    return fact[n] * invfact[k] % P * invfact[n - k] % P


def falling(x: int, r: int) -> int:
    ans = 1
    for j in range(r):
        ans = ans * (x - j) % P
    return ans


# Full recurrence: sum_{k=0}^n C(n+1,k) B_k = 0.
NMAX = 2 * B1
bern = [0] * (NMAX + 1)
bern[0] = 1
for n in range(1, NMAX + 1):
    total = 0
    for k in range(n):
        total = (total + choose(n + 1, k) * bern[k]) % P
    bern[n] = -total * pow(n + 1, P - 2, P) % P

# Sanity checks for the convention B_1=-1/2 and vanishing odd values.
assert bern[1] == -(P + 1) // 2 % P
assert all(bern[n] == 0 for n in range(3, NMAX + 1, 2))


def det_subset(mat: list[list[int]]) -> int:
    """Determinant by row-wise subset expansion, O(n^2 2^n)."""
    n = len(mat)
    assert all(len(row) == n for row in mat)
    dp = {0: 1}
    for r in range(n):
        nxt: dict[int, int] = {}
        for mask, value in dp.items():
            for j in range(n):
                if mask >> j & 1:
                    continue
                # Appending column j creates one inversion for each
                # previously chosen column greater than j.
                inversions = (mask >> (j + 1)).bit_count()
                term = value * mat[r][j]
                if inversions & 1:
                    term = -term
                newmask = mask | (1 << j)
                nxt[newmask] = (nxt.get(newmask, 0) + term) % P
        dp = nxt
    return dp[(1 << n) - 1] % P


def source_matrix(b: int) -> list[list[int]]:
    rows: list[list[int]] = []
    for t in range(b):
        row: list[int] = []
        for k in range(b):
            m = t + k - A + 1
            mu = 0 if m < 0 else bern[2 * m] * invfact[2 * m] % P
            first = fact[2 * b + 2 * t - 2 * A + 1] * invfact[2 * b - 2 * k] % P
            second = 0
            if k < A:
                second = fact[2 * t + 1] * invfact[2 * A - 2 * k] % P
            row.append(mu * (first + second) % P)
        rows.append(row)
    return rows


def retained_matrix(b: int) -> list[list[int]]:
    rows: list[list[int]] = []
    for i in range(A):
        n = b - A + i
        row: list[int] = []
        for ell in range(A):
            N = 2 * (n - ell) + 1
            R = 2 * b - 2 * A + 2 + 2 * ell

            f = invfact[2 * ell + 1]
            for r in range(2 * ell):
                f = f * (2 * n - r) % P
                f = f * (2 * n + 3 + r) % P

            correction = 0
            for h in range(1, 2 * i + 2, 2):
                delta = 0
                for j in range(h + 1):
                    z = N - j
                    w = (z + 2 * ell + 1) * falling(2 * n + 2 * ell + z + 1, 2 * i)
                    delta += (-1) ** (h - j) * comb(h, j) * w
                newton = (delta % P) * invfact[h] % P
                index = A - i + ell + (h - 1) // 2
                u = 2 * bern[2 * (b - index)] % P
                correction = (correction + newton * falling(N, h) * u) % P

            denom = (2 * n + 1) * (2 * n + 2) % P
            denom = denom * fact[2 * ell + 2] % P
            denom = denom * fact[N] % P
            coeff = fact[R] * pow(denom, P - 2, P) % P
            row.append((2 * f + coeff * correction) % P)
        rows.append(row)
    return rows


residues: list[int] = []
for b in range(B0, B1 + 1):
    matrix = source_matrix(b) if b < SWITCH else retained_matrix(b)
    residues.append(det_subset(matrix))

recorded = [int(x) for x in CERT["residues"]]
assert residues == recorded
assert all(residues)
payload = ",".join(map(str, residues)).encode("ascii")
assert sha256(payload).hexdigest() == CERT["residue_sha256"]
print("PASS: independent full replay")
print(f"  cases: {len(residues)}")
print(f"  prime: {P}")
print(f"  sha256: {CERT['residue_sha256']}")
