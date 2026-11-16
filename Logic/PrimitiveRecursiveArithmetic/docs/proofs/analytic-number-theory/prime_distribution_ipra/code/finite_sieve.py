#!/usr/bin/env python3
"""Exact rational Selberg-sieve examples and bounded consistency checks.

This is NOT a proof checker for iPRA, and a successful finite check is NOT a
proof of a universal theorem. The accompanying mathematical proof supplies the
universal argument. This script detects normalization and endpoint mistakes in
its finite identities, using only Python's standard library and exact integers.
"""

from fractions import Fraction
from math import gcd, lcm
import argparse
import json


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, n))


def phi(n: int) -> int:
    if n < 1:
        raise ValueError("phi is used only on positive integers")
    return sum(gcd(a, n) == 1 for a in range(1, n + 1))


def mu(n: int) -> int:
    if n < 1:
        raise ValueError("mu is used only on positive integers")
    sign = 1
    for p in range(2, n + 1):
        if prime(p) and n % p == 0:
            if n % (p * p) == 0:
                return 0
            sign = -sign
    return sign


def harmonic(z: int) -> Fraction:
    return sum((Fraction(1, n) for n in range(1, z + 1)), Fraction(0))


def pi_ap(x: int, q: int, a: int) -> int:
    if q < 1:
        raise ValueError("q must be positive")
    return sum(prime(n) and n % q == a % q for n in range(1, x + 1))


def selberg_data(q: int, z: int):
    if q < 1 or z < 1:
        raise ValueError("q,z must be positive")
    ds = [d for d in range(1, z + 1) if mu(d) and gcd(d, q) == 1]
    g = sum((Fraction(1, phi(d)) for d in ds), Fraction(0))
    ys = {d: Fraction(mu(d), phi(d)) / g for d in ds}
    weights = {
        d: d * sum((mu(r // d) * ys[r] for r in ds if r % d == 0), Fraction(0))
        for d in ds
    }
    return ds, g, ys, weights


def check_case(q: int, z: int) -> None:
    ds, g, ys, weights = selberg_data(q, z)
    assert weights[1] == 1
    assert all(abs(w) <= 1 for w in weights.values())
    for r in ds:
        assert ys[r] == sum(
            (weights[d] / d for d in ds if d % r == 0), Fraction(0)
        )
    quad = sum(
        (weights[d] * weights[e] / lcm(d, e) for d in ds for e in ds),
        Fraction(0),
    )
    assert quad == 1 / g
    assert g >= Fraction(phi(q), q) * harmonic(z)
    for x in (0, 1, 2, 3, 11, 40, 80, 200):
        for a in range(q):
            if gcd(a, q) != 1:
                continue
            count = pi_ap(x, q, a)
            first = Fraction(x, q) / g + z * z + z
            second = Fraction(x, phi(q)) / harmonic(z) + z * z + z
            assert count <= first <= second


def self_check() -> dict:
    cases = 0
    for q in range(1, 13):
        for z in range(1, 25):
            check_case(q, z)
            cases += 1
    return {
        "status": "passed",
        "q_z_identity_cases": cases,
        "q_range": [1, 12],
        "z_range": [1, 24],
        "x_samples": [0, 1, 2, 3, 11, 40, 80, 200],
        "arithmetic": "exact Python integers and fractions.Fraction",
        "scope": "bounded consistency checks, not a universal proof or an iPRA derivation",
    }


def example(x: int, q: int, a: int, z: int) -> dict:
    if gcd(a, q) != 1:
        raise ValueError("a and q must be coprime")
    ds, g, ys, weights = selberg_data(q, z)
    check_case(q, z)
    return {
        "parameters": {"x": x, "q": q, "a": a, "z": z},
        "pi_ap": pi_ap(x, q, a),
        "D": ds,
        "G": str(g),
        "H": str(harmonic(z)),
        "weights": {str(d): str(weights[d]) for d in ds},
        "diagonal_values": {str(d): str(ys[d]) for d in ds},
        "G_lower_bound": str(Fraction(phi(q), q) * harmonic(z)),
        "sieve_upper_bound": str(Fraction(x, q) / g + z * z + z),
        "harmonic_upper_bound": str(Fraction(x, phi(q)) / harmonic(z) + z * z + z),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-check", action="store_true")
    parser.add_argument("--x", type=int, default=10000)
    parser.add_argument("--q", type=int, default=6)
    parser.add_argument("--a", type=int, default=1)
    parser.add_argument("--z", type=int, default=12)
    args = parser.parse_args()
    result = self_check() if args.self_check else example(args.x, args.q, args.a, args.z)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
