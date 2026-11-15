#!/usr/bin/env python3
"""Finite sanity checks for the constructive reciprocal-prime proof.

This script does not prove the theorem and is not a substitute for the iPRA
or Lean formalization.  It checks the central finite identities and
inequalities on modest sample ranges using exact Python integers/Fractions.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, factorial
from pathlib import Path


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def primes_up_to(n: int) -> list[int]:
    return [p for p in range(2, n + 1) if is_prime(p)]


def prod(values: list[int]) -> int:
    out = 1
    for value in values:
        out *= value
    return out


def prime_data(n: int) -> tuple[int, int, int]:
    ps = primes_up_to(n)
    q = prod(ps)
    r = sum(q // p for p in ps)
    d = prod([p - 1 for p in ps])
    return q, r, d


def harmonic_data(n: int) -> tuple[int, int]:
    f = factorial(n)
    t = sum(f // m for m in range(1, n + 1))
    return f, t


def harmonic(n: int) -> Fraction:
    return sum((Fraction(1, m) for m in range(1, n + 1)), Fraction(0, 1))


def euler_product(n: int) -> Fraction:
    out = Fraction(1, 1)
    for p in primes_up_to(n):
        out *= Fraction(p, p - 1)
    return out


def prime_sum(n: int) -> Fraction:
    return sum((Fraction(1, p) for p in primes_up_to(n)), Fraction(0, 1))


def check_local_factor(limit: int = 200) -> None:
    for p in range(2, limit + 1):
        assert p**p <= 4 * (p - 1) ** p, p


def check_binomial_bound(limit: int = 100) -> None:
    for a in range(1, limit + 1):
        lhs = (a + 1) ** a
        rhs = 3 * a**a
        assert lhs <= rhs, a
        # Check the termwise proof used in the paper.
        for j in range(a + 1):
            assert comb(a, j) * factorial(j) <= a**j
        for j in range(1, a + 1):
            assert 2 ** (j - 1) <= factorial(j)


def check_euler_domination(limit: int = 30) -> None:
    for n in range(1, limit + 1):
        assert harmonic(n) <= euler_product(n), n
        f, t = harmonic_data(n)
        q, _, d = prime_data(n)
        assert t * d <= f * q, n


def check_power_cleared(limit: int = 12) -> None:
    # The exponent Q_n grows very rapidly; n <= 12 already checks nontrivial
    # exact big-integer instances.
    for n in range(2, limit + 1):
        q, r, d = prime_data(n)
        assert q**q <= 4**r * d**q, n


def check_dyadic(limit_t: int = 6) -> None:
    for t in range(limit_t + 1):
        n = 2 ** (2 * t)
        assert harmonic(n) >= 1 + t, t
        f, hnum = harmonic_data(n)
        assert hnum >= (1 + t) * f, t


def check_main_small() -> list[str]:
    lines: list[str] = []
    for k in (0, 1):
        n = 2 ** (2 * 4**k)
        s = prime_sum(n)
        assert s > k
        lines.append(f"k={k}: W(k)={n}, prime reciprocal sum={s} > {k}")
    # k=2 has W(2)=2^32, too large for a direct enumeration in this sanity
    # checker; the mathematical proof is uniform and does not enumerate W(k).
    lines.append("k=2 and above: intentionally not enumerated; proof is symbolic/uniform.")
    return lines


def main() -> None:
    check_local_factor()
    check_binomial_bound()
    check_euler_domination()
    check_power_cleared()
    check_dyadic()
    examples = check_main_small()

    report = [
        "Finite sanity-check report",
        "==========================",
        "",
        "PASS: local factor p^p <= 4 (p-1)^p for 2 <= p <= 200.",
        "PASS: binomial/factorial bounds for 1 <= a <= 100.",
        "PASS: H_n <= Euler product for 1 <= n <= 30.",
        "PASS: cross-multiplied Euler domination for 1 <= n <= 30.",
        "PASS: Q_n^Q_n <= 4^R_n D_n^Q_n for 2 <= n <= 12.",
        "PASS: H_(2^(2t)) >= 1+t for 0 <= t <= 6.",
        "",
        *examples,
        "",
        "These checks are diagnostic only; they are not a formal proof.",
    ]
    text = "\n".join(report) + "\n"
    out = Path(__file__).resolve().parents[1] / "artifacts" / "verification_report.txt"
    out.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
