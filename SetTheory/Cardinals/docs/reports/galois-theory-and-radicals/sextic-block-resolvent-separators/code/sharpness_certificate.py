#!/usr/bin/env python3
"""Produce and verify an exact modular certificate for 195 distinct bad parameters.

The certificate is a polynomial Bezout identity modulo a trial-division-checked
prime. No floating-point arithmetic, external CAS, or Galois-group oracle is used.
Coefficients are stored in ascending order. This is not a kernel-checked proof.
"""
from __future__ import annotations
from math import isqrt
from pathlib import Path
import json
import verify as v

MODULUS = 1_000_003
ROOTS = (1, 4, 10, 23, 51, 109)


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] = x % p
    for i, x in enumerate(b):
        out[i] = (out[i] + x) % p
    return trim(out)


def neg(a: list[int], p: int) -> list[int]:
    return [(-x) % p for x in a]


def mul(a: list[int], b: list[int], p: int) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j] + x*y) % p
    return trim(out)


def divrem(a: list[int], b: list[int], p: int) -> tuple[list[int], list[int]]:
    if b == [0]:
        raise ZeroDivisionError('Polynomial division by zero')
    a = a.copy()
    q = [0] * max(1, len(a) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        d = len(a) - len(b)
        c = a[-1] * inv % p
        q[d] = c
        for i, x in enumerate(b):
            a[i+d] = (a[i+d] - c*x) % p
        trim(a)
    return trim(q), a


def xgcd(a: list[int], b: list[int], p: int):
    s0, s1, t0, t1 = [1], [0], [0], [1]
    while b != [0]:
        q, r = divrem(a, b, p)
        a, b = b, r
        s0, s1 = s1, add(s0, neg(mul(q, s1, p), p), p)
        t0, t1 = t1, add(t0, neg(mul(q, t1, p), p), p)
    c = pow(a[-1], -1, p)
    return ([c*x % p for x in a], [c*x % p for x in s0],
            [c*x % p for x in t0])


def obstruction_mod(roots: tuple[int, ...], p: int) -> list[int]:
    v.validate_roots(roots)
    factors = []
    for i, j in v.EDGES:
        factors.append([-roots[i]*roots[j], roots[i]+roots[j], 1])
    data = [v.pair_data(roots, m) for m in v.MATCHINGS]
    for i, j in v.DISJOINT:
        a, b, c = data[i]
        d, e, f = data[j]
        factors.append([f-c, b-e, a-d])
    for a, b in v.PAIR_PAIRS:
        factors.append([roots[b[0]]*roots[b[1]]-roots[a[0]]*roots[a[1]],
                        roots[a[0]]+roots[a[1]]-roots[b[0]]-roots[b[1]]])
    out = [1]
    for factor in factors:
        out = mul(out, [x % p for x in factor], p)
    return out


def create_and_check() -> dict:
    p = MODULUS
    assert p >= 2 and all(p % d for d in range(2, isqrt(p)+1))
    polynomial = obstruction_mod(ROOTS, p)
    derivative = trim([i*polynomial[i] % p for i in range(1, len(polynomial))])
    gcd, a, b = xgcd(polynomial, derivative, p)
    assert len(polynomial) == 196
    assert polynomial[0] != 0
    assert gcd == [1]
    # This is the independently checkable certificate equation.
    assert add(mul(a, polynomial, p), mul(b, derivative, p), p) == [1]
    assert all((x-y) % p for i, x in enumerate(ROOTS) for y in ROOTS[i+1:])
    return {'roots': ROOTS, 'modulus': p, 'prime_checked_by_trial_division': True,
            'coefficient_order': 'ascending', 'obstruction_mod_p': polynomial,
            'bezout_a': a, 'bezout_b': b,
            'identity': 'bezout_a * E + bezout_b * derivative(E) = 1 (mod p)',
            'degree': len(polynomial)-1, 'constant_mod_p': polynomial[0],
            'leading_mod_p': polynomial[-1],
            'conclusion': 'The exact integer obstruction has degree 195 and 195 distinct nonzero complex roots.'}


if __name__ == '__main__':
    result = create_and_check()
    path = Path(__file__).resolve().parents[1] / 'checks' / 'sharpness_certificate.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: value for k, value in result.items()
                      if k not in ('obstruction_mod_p', 'bezout_a', 'bezout_b')}, indent=2))
