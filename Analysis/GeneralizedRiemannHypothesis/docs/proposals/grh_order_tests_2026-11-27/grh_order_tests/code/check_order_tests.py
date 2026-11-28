#!/usr/bin/env python3
"""Exact checks for the proposed finite-field label replacement.

Python 3 standard library only. No floating-point arithmetic is used.
The proof is in order_tests.tex; these are regression and counterexample checks.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
import json
from pathlib import Path
import random


def factor(n: int) -> dict[int, int]:
    out = {}
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                e += 1
                n //= p
            out[p] = e
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = 1
    return out


def valuation(n: int, p: int) -> int:
    assert n > 0 and p > 1
    e = 0
    while n % p == 0:
        e += 1
        n //= p
    return e


def phi(n: int) -> int:
    for p in factor(n):
        n = n // p * (p - 1)
    return n


def density(q: int, level: int) -> Fraction:
    assert level % 3 == 0 and (q - 1) % (level * level) == 0
    value = Fraction(2, 3)
    for p, n in factor(level).items():
        if p != 3:
            value *= 1 - Fraction(1, p ** n)
    return value


def norm_order_ok(norm_order: int, q: int, level: int) -> bool:
    return valuation(norm_order, 3) == valuation(q - 1, 3) and all(
        p == 3 or valuation(norm_order, p) > valuation(q - 1, p) - n
        for p, n in factor(level).items()
    )


def qualifies(a: int, q: int, rank: int, level: int) -> bool:
    """The element is g**a in a cyclic group of order q**rank - 1."""
    m = q**rank - 1
    b = q ** (rank // 3)
    norm_order = (q - 1) // gcd(a, q - 1)
    return norm_order_ok(norm_order, q, level) and (a * 3 * (b - 1)) % m != 0


def orbit_degree(a: int, q: int, rank: int) -> int:
    m = q**rank - 1
    a %= m
    x = a
    for degree in range(1, rank + 1):
        x = (x * q) % m
        if x == a:
            return degree
    raise AssertionError("Frobenius did not close")


def check_cyclic_case(q: int, rank: int, level: int, exhaustive: bool) -> dict:
    assert factor(q) and len(factor(q)) == 1, "q must be a prime power"
    assert rank >= 3 and set(factor(rank)) == {3}
    m, b = q**rank - 1, q ** (rank // 3)
    h = 3 * (b - 1)
    c = (b * b + b + 1) // 3
    assert h * c == m and gcd(h, c) == 1 and gcd(c, q - 1) == 1
    expected = density(q, level) * (m - h)
    assert expected.denominator == 1
    expected = expected.numerator
    assert expected % rank == 0

    if exhaustive:
        good = [a for a in range(m) if qualifies(a, q, rank, level)]
        assert len(good) == expected
    else:
        rng = random.Random(q * 10000 + rank * 100 + level)
        candidates = [0, 1, 2, 3, c, h, m - 1]
        candidates += [rng.randrange(m) for _ in range(2500)]
        good = [a for a in candidates if qualifies(a, q, rank, level)]

    # All checks are exhaustive for the two small cyclic examples. Larger cases
    # exhaust the count and use an explicitly deterministic structural sample.
    if len(good) <= 20000:
        tested = good
    else:
        rng = random.Random(q + rank)
        tested = rng.sample(good, min(1500, len(good)))
    prime_factors = factor(m)
    for a in tested:
        assert orbit_degree(a, q, rank) == rank
        assert a % c != 0
        no = (q - 1) // gcd(a, q - 1)
        assert no % level == 0
        # Check the definition by power tests in the base cyclic group directly.
        assert (a * ((q - 1) // 3)) % (q - 1) != 0
        for p, n in factor(level).items():
            if p != 3:
                assert (a * ((q - 1) // (p**n))) % (q - 1) != 0
                assert ((q - 1) // (p**n)) % level == 0
        assert ((q - 1) // 3) % level == 0
        # Maximum relevant exponent for each prime factor suffices: if a lower
        # power entered a proper subfield, every higher power would also do so.
        for ell, e in prime_factors.items():
            assert orbit_degree(a * ell**e, q, rank) == rank
        # Primes outside m give an invertible power map on the cyclic group.
        for ell in (5, 11, 17):
            if ell not in prime_factors:
                assert orbit_degree(a * ell**4, q, rank) == rank
        for j in range(level):
            assert qualifies((a + j * (m // level)) % m, q, rank, level)
        for j in range(rank):
            assert qualifies(a * q**j % m, q, rank, level)

    # Generator powers are always retained. This is an independent subset check.
    primitive_test = range(m) if m <= 60000 else range(1, 2000)
    for a in primitive_test:
        if gcd(a, m) == 1:
            assert qualifies(a, q, rank, level)
    return {
        "q": q, "rank": rank, "N": level,
        "norm_density": str(density(q, level)),
        "root_count": expected, "polynomial_count": expected // rank,
        "primitive_polynomial_count": phi(m) // rank,
        "exhaustive_root_count": exhaustive,
        "structural_roots_checked": len(tested),
        "prime_factors_of_group_order": prime_factors,
    }


class CubicField:
    """F_p[X]/(X^3 + b X^2 + c X + d), with irreducibility checked separately."""
    def __init__(self, p: int, b: int, c: int, d: int):
        self.p, self.modulus = p, (d, c, b)

    def mul(self, a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
        z = [0] * 5
        for i in range(3):
            for j in range(3):
                z[i + j] += a[i] * b[j]
        for k in (4, 3):
            for j in range(3):
                z[k - 3 + j] -= z[k] * self.modulus[j]
        return tuple(x % self.p for x in z[:3])

    def power(self, a: tuple[int, ...], n: int) -> tuple[int, ...]:
        ans = (1, 0, 0)
        while n:
            if n & 1:
                ans = self.mul(ans, a)
            a = self.mul(a, a)
            n >>= 1
        return ans


def check_all_cubics(p: int = 19, level: int = 3) -> dict:
    assert factor(p) == {p: 1}
    m = p**3 - 1
    m_factors = factor(m)
    e = (m // (p - 1))
    x, one = (0, 1, 0), (1, 0, 0)
    counts = {"all_monic": p**3, "irreducible": 0, "qualifying": 0, "primitive": 0}
    example = None
    for b, c, d in product(range(p), repeat=3):
        if any((((z + b) * z + c) * z + d) % p == 0 for z in range(p)):
            continue
        counts["irreducible"] += 1
        f = CubicField(p, b, c, d)
        assert f.power(x, m) == one
        norm = f.power(x, e)
        assert norm == ((-d) % p, 0, 0)
        norm_order = p - 1
        for prime in factor(p - 1):
            while norm_order % prime == 0 and pow(norm[0], norm_order // prime, p) == 1:
                norm_order //= prime
        good = norm_order_ok(norm_order, p, level) and f.power(x, 3 * (p - 1)) != one
        primitive = all(f.power(x, m // prime) != one for prime in m_factors)
        counts["qualifying"] += good
        counts["primitive"] += primitive
        assert not primitive or good
        if good:
            for ell, v in m_factors.items():
                z = f.power(x, ell**v)
                assert f.power(z, p) != z
            for lam in range(1, p):
                if pow(lam, level, p) == 1:
                    z = (0, lam, 0)
                    nn = f.power(z, e)[0]
                    no = p - 1
                    for prime in factor(p - 1):
                        while no % prime == 0 and pow(nn, no // prime, p) == 1:
                            no //= prime
                    assert norm_order_ok(no, p, level)
                    assert f.power(z, 3 * (p - 1)) != one
            if not primitive and example is None:
                order = m
                for prime in m_factors:
                    while order % prime == 0 and f.power(x, order // prime) == one:
                        order //= prime
                example = {"coefficients_ascending": [d, c, b, 1],
                           "root_order": order, "norm": norm[0], "norm_order": norm_order,
                           "root_power_54": list(f.power(x, 54))}
    expected = density(p, level) * (p**3 - 1 - 3 * (p - 1)) / 3
    assert counts["qualifying"] == expected
    assert counts["primitive"] == phi(m) // 3
    return {"q": p, "rank": 3, "N": level, **counts, "nonprimitive_example": example}


def check_counterexamples() -> dict:
    q, r, level = 19, 3, 3
    m = q**r - 1
    assert qualifies(2, q, r, level) and gcd(2, m) != 1
    # Dropping the root-exclusion test admits an element killed into the base field by cubing.
    a = 127
    assert norm_order_ok((q - 1) // gcd(a, q - 1), q, level)
    assert orbit_degree(3 * a, q, r) == 1
    # Dropping full 3-primary norm admits an element killed into the base field by a 127th power.
    a = 27
    assert a * 3 * (q - 1) % m != 0
    assert orbit_degree(127 * a, q, r) == 1
    # Merely requiring N | ord(norm) does not survive Nth-root scaling.
    q, level = 37, 6
    m = q**3 - 1
    a, scaled = 2, 2 + m // 2  # multiply by -1 in the base field
    assert (q - 1) // gcd(a, q - 1) == 18
    assert (q - 1) // gcd(scaled, q - 1) == 9
    assert 18 % level == 0 and 9 % level != 0
    # The uniform density is not asserted under the general hypotheses alone.
    assert density(37, 6) == Fraction(1, 3) < Fraction(1, 2)
    # With rank 6 the tests can pass, even with initial irreducibility, while
    # a power of 2 collapses the degree. The theorem deliberately excludes it.
    q, r, level, a = 19, 6, 3, 1715
    m = q**r - 1
    assert m // gcd(a, m) == 27432
    assert (q - 1) // gcd(a, q - 1) == 18
    assert qualifies(a, q, r, level)
    assert orbit_degree(a, q, r) == 6
    assert orbit_degree(a * 8, q, r) == 3
    return {"nonprimitive_root_exponent": 2,
            "drop_exclusion": {"q": 19, "a": 127, "power": 3, "degree_after": 1},
            "drop_full_three_part": {"q": 19, "a": 27, "power": 127, "degree_after": 1},
            "drop_extra_norm_power": {"q": 37, "N": 6, "norm_orders": [18, 9]},
            "general_density_below_half": "q=37, N=6, density=1/3",
            "rank_not_three_power": {"q": 19, "rank": 6, "N": 3,
                "root_exponent": 1715, "root_order": 27432, "norm_order": 18,
                "initial_degree": 6, "power": 8, "degree_after": 3}}


def check_uniform_estimates() -> dict:
    # Exact telescoping majorant; no numerical zeta estimate is assumed.
    for n in range(2, 1000):
        assert n**6 >= 16 * n * (n - 1)
    prime_set = [p for p in range(2, 500) if len(factor(p)) == 1 and factor(p).get(p) == 1]
    product_bound = Fraction(2, 3)
    for p in prime_set:
        if p != 3:
            product_bound *= 1 - Fraction(1, p**6)
    assert product_bound > Fraction(5, 8)
    for b in range(2, 2000):
        assert 2 * (b**3 - 3 * b + 2) >= b**3
    for b in range(3, 2000):
        assert Fraction(3, b*b + b + 1) <= Fraction(1, 4)
        assert Fraction(b**3 - 1, b**3) >= Fraction(3, 4)
    assert (1 - Fraction(1, 3) - Fraction(1, 16) - Fraction(1, 4)) * Fraction(3, 4) == Fraction(17, 64)
    assert Fraction(5, 8) * Fraction(1, 2) > Fraction(1, 4)
    return {"uniform_norm_density_lower_bound": "5/8",
            "uniform_polynomial_fraction_lower_bound": "5/(16*r)",
            "union_bound_polynomial_fraction_lower_bound": "17/(64*r)",
            "convenient_complement_exponent": "1/(4*r)",
            "caveat": "The exponent bounds a uniform weighted complement count, not individual Plancherel mass."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    cases = [(19, 3, 3, True), (37, 3, 6, True), (73, 3, 6, True),
             (109, 3, 6, True), (64, 3, 3, True), (19, 9, 3, False)]
    result = {"status": "PASS", "arithmetic": "exact integer and rational arithmetic",
              "cyclic_cases": [check_cyclic_case(*case) for case in cases],
              "independent_cubic_enumeration": check_all_cubics(),
              "counterexamples": check_counterexamples(),
              "uniform_estimates": check_uniform_estimates(),
              "formal_status": "Regression checks only; no Lean build or kernel replay performed."}
    encoded = json.dumps(result, indent=2)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded + "\n")
    print(encoded)


if __name__ == "__main__":
    main()
