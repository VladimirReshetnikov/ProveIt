#!/usr/bin/env python3
"""Exact finite checks for scale-moderate Hahn interpolation.

Uses only the Python standard library. These are finite algebra and ordered-group
checks, not verification of the infinite theorems or a proof-assistant certificate.
Run: python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable

Poly = tuple[F, ...]
ZERO: Poly = (F(0),)
ONE: Poly = (F(1),)
X: Poly = (F(0), F(1))
COUNTS: dict[str, int] = {}


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f"Failed check in {category}")
    COUNTS[category] = COUNTS.get(category, 0) + 1


def poly(values: Iterable[int | F]) -> Poly:
    a = [F(x) for x in values]
    if not a:
        return ZERO
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return tuple(a)


def add(a: Poly, b: Poly) -> Poly:
    return poly((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b))))


def neg(a: Poly) -> Poly:
    return poly(-x for x in a)


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, neg(b))


def scalar(a: Poly, c: int | F) -> Poly:
    return poly(F(c) * x for x in a)


def mul(a: Poly, b: Poly) -> Poly:
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return poly(out)


def power(a: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("Use invmod for negative modular powers")
    out = ONE
    while n:
        if n & 1:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def divmodp(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    if b == ZERO:
        raise ZeroDivisionError("zero polynomial")
    r = list(a)
    q = [F(0)] * max(1, len(a) - len(b) + 1)
    while len(r) >= len(b) and poly(r) != ZERO:
        offset = len(r) - len(b)
        c = r[-1] / b[-1]
        q[offset] += c
        for j, bj in enumerate(b):
            r[offset + j] -= c * bj
        r = list(poly(r))
    return poly(q), poly(r)


def rem(a: Poly, w: Poly) -> Poly:
    return divmodp(a, w)[1]


def invmod(a: Poly, w: Poly) -> Poly:
    r0, r1, s0, s1 = w, rem(a, w), ZERO, ONE
    while r1 != ZERO:
        q, r2 = divmodp(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, sub(s0, mul(q, s1))
    if len(r0) != 1 or r0[0] == 0:
        raise ValueError("polynomial class is not a unit")
    return rem(scalar(s0, 1 / r0[0]), w)


def scale_variable(a: Poly, s: F) -> Poly:
    return poly(c * s**j for j, c in enumerate(a))


def evaluate(a: Poly, x: F) -> F:
    out = F(0)
    for c in reversed(a):
        out = out * x + c
    return out


def determinant(matrix: list[list[F]]) -> F:
    a = [row[:] for row in matrix]
    n = len(a)
    out = F(1)
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            return F(0)
        if p != j:
            a[p], a[j] = a[j], a[p]
            out = -out
        pivot = a[j][j]
        out *= pivot
        for i in range(j + 1, n):
            c = a[i][j] / pivot
            for k in range(j + 1, n):
                a[i][k] -= c * a[j][k]
    return out


def norm_in_quotient(g: Poly, w: Poly) -> F:
    d = len(w) - 1
    columns = [rem(mul(g, power(X, j)), w) for j in range(d)]
    matrix = [[col[i] if i < len(col) else F(0) for col in columns]
              for i in range(d)]
    return determinant(matrix)


def finite_algebra_checks() -> None:
    rng = random.Random(22092026)
    scales = [F(2), F(17), F(103)]
    for case in range(18):
        roots: list[list[tuple[F, int]]] = []
        ws: list[Poly] = []
        ps: list[Poly] = []
        js: list[Poly] = []
        for n, s in enumerate(scales):
            # Near-coincident rational roots test the exact confluent algebra.
            us = [F(1)] if (case + n) % 3 == 0 else [F(1), F(102, 101)]
            data = [(u, 1 + rng.randrange(2)) for u in us]
            w = ONE
            for u, m in data:
                w = mul(w, power(poly([-u, 1]), m))
            p = scalar(scale_variable(w, 1 / s), 1 / w[0])
            j = poly(F(rng.randrange(-7, 8), rng.randrange(1, 8))
                     for _ in range(len(w) - 1))
            roots.append(data)
            ws.append(w)
            ps.append(p)
            js.append(j)
        total = ONE
        for p in ps:
            total = mul(total, p)
        hs: list[Poly] = []
        for n, (s, w, j) in enumerate(zip(scales, ws, js)):
            q_global, residual = divmodp(total, ps[n])
            check(residual == ZERO, "exact_product_division")
            q = rem(scale_variable(q_global, s), w)
            qi = invmod(q, w)
            xi = invmod(X, w)
            check(rem(mul(q, qi), w) == ONE, "block_inverse")
            check(rem(mul(X, xi), w) == ONE, "coordinate_inverse")
            N = (case + n) % 7
            R = rem(mul(mul(power(xi, N), qi), j), w)
            H = mul(mul(q_global, scale_variable(power(X, N), 1 / s)),
                    scale_variable(R, 1 / s))
            hs.append(H)
            for h, (sh, wh) in enumerate(zip(scales, ws)):
                actual = rem(scale_variable(H, sh), wh)
                check(actual == (j if h == n else ZERO), "cardinal_block_jets")
            expected_norm = F(1)
            for u, multiplicity in roots[n]:
                expected_norm *= evaluate(j, u)**multiplicity
            check(norm_in_quotient(j, w) == expected_norm,
                  "quotient_norm_root_product")
        interpolant = ZERO
        for h in hs:
            interpolant = add(interpolant, h)
        for s, w, j in zip(scales, ws, js):
            check(rem(scale_variable(interpolant, s), w) == j,
                  "simultaneous_hermite_interpolation")

    epsilon = F(1, 1009)
    J = scalar(poly([-1, 1]), 1 / epsilon)
    check(evaluate(J, F(1)) == 0, "collision_example")
    check(evaluate(J, F(1) + epsilon) == 1, "collision_example")


Vec = tuple[F, ...]
DIM = 9


def vadd(a: Vec, b: Vec) -> Vec:
    return tuple(x + y for x, y in zip(a, b))


def vmul(c: F | int, a: Vec) -> Vec:
    return tuple(F(c) * x for x in a)


def basis(n: int) -> Vec:
    return tuple(F(int(j == n)) for j in range(DIM))


def compare(a: Vec, b: Vec) -> int:
    for x, y in zip(reversed(a), reversed(b)):
        if x != y:
            return 1 if x > y else -1
    return 0


def in_scale_subgroup(a: Vec, n: int) -> bool:
    return all(x == 0 for x in a[n + 1:])


def valuation_checks() -> None:
    rng = random.Random(20260922)
    zero = (F(0),) * DIM
    for n in range(1, DIM - 1):
        lam = basis(n)
        for _ in range(100):
            M = rng.randrange(0, 300)
            mu = vmul(-M, lam)
            r = vadd(vmul(F(1, 2), lam), vmul(-rng.randrange(0, 20), basis(n - 1)))
            beta = vmul(rng.randrange(0, 20), basis(n - 1))
            N = 2 * M + 2
            bound = vadd(vadd(mu, beta), vmul(N, vadd(lam, vmul(-1, r))))
            check(compare(r, vmul(F(1, 2), lam)) <= 0, "admissible_radius")
            check(compare(bound, lam) >= 0, "suppression_inequality")
        earlier = zero
        for j in range(n):
            earlier = vadd(earlier, basis(j))
        # Here there are n earlier roots; indexing is zero-based in this code.
        correction = vadd(vmul(1 - n, lam), earlier)
        for theta in [vmul(17, lam), basis(n + 1),
                      vadd(basis(n + 1), vmul(-1000, lam))]:
            value = vadd(theta, correction)
            check(in_scale_subgroup(value, n) == in_scale_subgroup(theta, n),
                  "sharp_separation_coset")
            if not in_scale_subgroup(theta, n):
                check(compare(value, zero) > 0, "boundary_positive_coset")
        beta = zero
        for j in range(n):
            beta = vadd(beta, vmul(j + 1, vadd(lam, vmul(-1, basis(j)))))
        check(compare(beta, zero) >= 0, "inverse_block_gain")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    finite_algebra_checks()
    valuation_checks()
    result = {
        "status": "PASS",
        "arithmetic": "exact rational arithmetic; reverse-lexicographic rational vectors",
        "random_seeds": [22092026, 20260922],
        "checks": COUNTS,
        "total_assertions": sum(COUNTS.values()),
        "scope": "finite polynomial identities and finite ordered-group inequalities only",
        "not_verified": ["infinite Hahn summability", "the full mathematical theorems",
                         "novelty", "Lean formalization"],
    }
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
