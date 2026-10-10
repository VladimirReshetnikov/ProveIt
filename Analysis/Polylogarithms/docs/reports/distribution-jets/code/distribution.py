#!/usr/bin/env python3
"""Exact finite distribution matrices and primitive-grid normal forms.

All arithmetic in this module uses fractions.Fraction. The rank theorem is
proved in the accompanying article; finite tests are regression checks only.
Residues are 0,...,q-1. Residue 0 denotes the endpoint 1 for Hurwitz values.
"""
from __future__ import annotations
from fractions import Fraction
from math import gcd
from typing import Mapping, Sequence

Q = Fraction


def factor(n: int) -> dict[int, int]:
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    out: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n: int) -> list[int]:
    out = [1]
    for p, e in factor(n).items():
        out = [d * p**j for d in out for j in range(e + 1)]
    return sorted(out)


def units(q: int) -> list[int]:
    if q < 1:
        raise ValueError("q must be positive")
    return [a for a in range(q) if gcd(a, q) == 1]


def phi(q: int) -> int:
    return len(units(q))


def order(p: int, m: int) -> int:
    if m == 1:
        return 1
    if gcd(p, m) != 1:
        raise ValueError("multiplicative order requires coprime arguments")
    z, h = p % m, 1
    while z != 1:
        z = z * p % m
        h += 1
    return h


def distribution_rows(q: int, weights: Mapping[int, Q | int],
                      composite: bool = False) -> list[list[Q]]:
    """Rows sum_{d*b=a} e_b - A_d e_a, at finite level q.

    A_d is multiplicative in the supplied prime weights. Composite rows are
    optional; the article proves that prime rows already generate them.
    """
    ps = factor(q)
    if set(weights) != set(ps):
        raise ValueError("provide exactly one weight for each prime dividing q")
    ds = divisors(q)[1:] if composite else list(ps)
    rows = []
    for d in ds:
        ad = Q(1)
        for p, e in factor(d).items():
            ad *= Q(weights[p]) ** e
        m = q // d
        for b in range(m):
            row = [Q(0) for _ in range(q)]
            for j in range(d):
                row[b + j * m] += 1
            row[d * b % q] -= ad
            rows.append(row)
    return rows


def rank(rows: Sequence[Sequence[Q | int]]) -> int:
    """Exact sparse Gaussian elimination, without floating-point arithmetic."""
    pivots: dict[int, dict[int, Q]] = {}
    for row in rows:
        v = {i: Q(a) for i, a in enumerate(row) if a}
        while v:
            c = min(v)
            if c not in pivots:
                scale = v[c]
                pivots[c] = {j: a / scale for j, a in v.items()}
                break
            scale = v[c]
            for j, a in pivots[c].items():
                value = v.get(j, Q(0)) - scale * a
                if value:
                    v[j] = value
                else:
                    v.pop(j, None)
    return len(pivots)


def primitive_matrix(q: int, s: int) -> list[list[Q]]:
    """Return C_{r,u}(s), the exact primitive-grid extension matrix.

    s is a nonzero integer. Positive s uses a convergent smooth-number sum;
    negative s uses its finite rational continuation. This is not an
    infinite-series evaluator at negative s.
    """
    if q < 2 or not isinstance(s, int) or s == 0:
        raise ValueError("q >= 2 and a nonzero integer s are required")
    us, ps = units(q), list(factor(q))
    cache: dict[int, dict[int, Q]] = {}
    result = []
    for r in range(q):
        g = gcd(r, q)
        m = q // g
        if g not in cache:
            coeff = {1 % m: Q(1)}
            for p in ps:
                if m % p == 0:
                    continue
                h, z = order(p, m), Q(p) ** (-s)
                denom = 1 - z**h
                if not denom:
                    raise ValueError("resonant primitive-grid coordinate")
                nxt: dict[int, Q] = {}
                for a, value in coeff.items():
                    power, residue = Q(1), a
                    for _ in range(h):
                        nxt[residue] = nxt.get(residue, Q(0)) + value * power / denom
                        power *= z
                        residue = residue * p % m
                coeff = nxt
            cache[g] = coeff
        a = r // g
        scale = Q(g) ** (-s)
        row = []
        for u in us:
            b = 0 if m == 1 else a * pow(u, -1, m) % m
            row.append(scale * cache[g].get(b, Q(0)))
        result.append(row)
    return result


def support_prediction(q: int, r: int) -> int:
    """Exact number of nonzero coefficients, for real s != 0."""
    r %= q
    g, us = gcd(r, q), units(q)
    m = q // g
    subgroup = {1 % m}
    for p in factor(q):
        if m % p == 0:
            continue
        subgroup = {a * pow(p, j, m) % m
                    for a in subgroup for j in range(order(p, m))}
    return len(us) // phi(m) * len(subgroup)


def verify_matrix(q: int, s: int) -> dict[str, int]:
    C = primitive_matrix(q, s)
    us = units(q)
    rows = distribution_rows(q, {p: Q(p)**s for p in factor(q)}, composite=True)
    for row in rows:
        nz = [(j, a) for j, a in enumerate(row) if a]
        for c in range(len(us)):
            assert sum(a * C[j][c] for j, a in nz) == 0
    for i, u in enumerate(us):
        assert C[u] == [Q(int(i == j)) for j in range(len(us))]
    for r in range(q):
        assert sum(bool(x) for x in C[r]) == support_prediction(q, r)
        saturated = sum((q // gcd(r, q)) % p != 0 for p in factor(q))
        sign = 1 if s > 0 or saturated % 2 == 0 else -1
        assert all(sign * x > 0 for x in C[r] if x)
    c0 = Q(q)**(-s)
    for p in factor(q):
        c0 /= 1 - Q(p)**(-s)
    assert all(x == c0 for x in C[0])
    return {"q": q, "s": s, "rows": len(rows), "columns": len(us)}
