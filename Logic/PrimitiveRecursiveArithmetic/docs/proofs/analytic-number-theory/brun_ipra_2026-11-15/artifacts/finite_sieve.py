#!/usr/bin/env python3
"""Exact finite arithmetic accompanying the constructive proof of Brun's theorem.

This module uses only the Python standard library.  Fractions are exact; finite
tests are diagnostics for the formulas, not a proof of their universal validity.
The proof and the iPRA induction audit are in the accompanying article.

Convention: B(N) includes smaller twin primes p < N, while T(X) counts p <= X.
The cutoff 2**(2**(q+13)) is intentionally returned symbolically, not evaluated.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from math import factorial, gcd, isqrt
from pathlib import Path


def is_prime(n: int) -> bool:
    """Bounded trial division; this includes the cases n = 0 and n = 1."""
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def factor(n: int) -> tuple[tuple[int, int], ...]:
    """Prime factorization by explicitly bounded loops, for n >= 1."""
    if n < 1:
        raise ValueError("factor expects a positive integer")
    residual = n
    answer = []
    for candidate in range(2, isqrt(n) + 1):
        exponent = 0
        for _ in range(n):
            if residual % candidate:
                break
            residual //= candidate
            exponent += 1
        if exponent:
            answer.append((candidate, exponent))
        if residual == 1:
            break
    if residual > 1:
        answer.append((residual, 1))
    return tuple(answer)


def squarefree(n: int) -> bool:
    return n >= 1 and all(e == 1 for _, e in factor(n))


def radical(n: int) -> int:
    result = 1
    for p, _ in factor(n):
        result *= p
    return result


def mobius(n: int) -> int:
    factors = factor(n)
    return 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)


def rho(d: int) -> int:
    """Root count for n(n+2) modulo a positive squarefree d."""
    if not squarefree(d):
        raise ValueError("rho is used only at positive squarefree arguments")
    result = 1
    for p, _ in factor(d):
        result *= 1 if p == 2 else 2
    return result


def g(d: int) -> Fraction:
    return Fraction(rho(d), d)


def h(d: int) -> Fraction:
    if not squarefree(d):
        raise ValueError("h is used only at positive squarefree arguments")
    result = Fraction(1)
    for p, _ in factor(d):
        local_rho = 1 if p == 2 else 2
        result *= Fraction(local_rho, p - local_rho)
    return result


def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


@dataclass(frozen=True)
class SieveData:
    z: int
    divisors: tuple[int, ...]
    G: Fraction
    y: dict[int, Fraction]
    lam: dict[int, Fraction]


def sieve_data(z: int) -> SieveData:
    if z < 1:
        raise ValueError("z must be positive")
    divisors = tuple(d for d in range(1, z + 1) if squarefree(d))
    total = sum((h(d) for d in divisors), Fraction())
    y = {d: mobius(d) * h(d) / total for d in divisors}
    lam = {
        d: sum(
            (mobius(r // d) * y[r] for r in divisors if r % d == 0),
            Fraction(),
        ) / g(d)
        for d in divisors
    }
    return SieveData(z, divisors, total, y, lam)


def quadratic_form(data: SieveData) -> Fraction:
    return sum(
        (data.lam[d] * data.lam[e] * g(lcm(d, e))
         for d in data.divisors for e in data.divisors),
        Fraction(),
    )


def root_residues(d: int) -> tuple[int, ...]:
    if d < 1:
        raise ValueError("modulus must be positive")
    return tuple(a for a in range(d) if a * (a + 2) % d == 0)


def root_count(X: int, d: int) -> int:
    return sum(n * (n + 2) % d == 0 for n in range(1, X + 1))


def sifted_count(X: int, z: int) -> int:
    primes = tuple(p for p in range(2, z + 1) if is_prime(p))
    return sum(
        all(n * (n + 2) % p for p in primes)
        for n in range(1, X + 1)
    )


def weighted_square_sum(X: int, data: SieveData) -> Fraction:
    return sum(
        (sum((data.lam[d] for d in data.divisors
              if n * (n + 2) % d == 0), Fraction()) ** 2
         for n in range(1, X + 1)),
        Fraction(),
    )


def twin(n: int) -> bool:
    return is_prime(n) and is_prime(n + 2)


def twin_count(X: int) -> int:
    return sum(twin(p) for p in range(1, X + 1))


def brun_partial_sum(N: int) -> Fraction:
    """B(N) = sum over smaller twin primes p < N; 5 occurs twice."""
    return sum(
        (Fraction(1, p) + Fraction(1, p + 2)
         for p in range(1, N) if twin(p)),
        Fraction(),
    )


def brun_integer_code(N: int) -> tuple[int, int]:
    """An explicit PR code A(N)/D(N), where D(N) = (N+1)!."""
    if N < 0:
        raise ValueError("N must be nonnegative")
    denominator = factorial(N + 1)
    numerator = sum(
        denominator // p + denominator // (p + 2)
        for p in range(1, N) if twin(p)
    )
    return numerator, denominator


def harmonic(s: int) -> Fraction:
    return sum((Fraction(1, n) for n in range(1, s + 1)), Fraction())


def radical_pair_masses(s: int) -> dict[int, Fraction]:
    masses: dict[int, Fraction] = defaultdict(Fraction)
    for a in range(1, s + 1):
        for b in range(1, s + 1):
            masses[radical(a * b)] += Fraction(1, a * b)
    return dict(masses)


def cutoff_description(q: int) -> str:
    if q < 0:
        raise ValueError("precision q must be nonnegative")
    return f"2^(2^({q}+13))"


def exact_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def verification_report() -> dict:
    """Run exact finite checks; raise AssertionError at the first discrepancy."""
    counts: dict[str, int] = defaultdict(int)
    for d in range(1, 101):
        if squarefree(d):
            assert len(root_residues(d)) == rho(d)
            counts["root_residue_counts"] += 1
            for X in (0, 1, 2, 7, 25, 100):
                assert abs(Fraction(root_count(X, d)) - X * g(d)) <= rho(d)
                counts["root_count_errors"] += 1
    selected_weights = []
    for z in range(1, 31):
        data = sieve_data(z)
        assert data.lam[1] == 1
        counts["lambda_one"] += 1
        assert quadratic_form(data) == 1 / data.G
        counts["quadratic_form_identities"] += 1
        for r in data.divisors:
            recovered = sum(
                (data.lam[d] * g(d) for d in data.divisors if d % r == 0),
                Fraction(),
            )
            assert recovered == data.y[r]
            assert abs(data.lam[r]) * rho(r) <= r
            counts["mobius_inversions"] += 1
            counts["coefficient_bounds"] += 1
        if z in (1, 5, 10, 30):
            selected_weights.append({
                "z": z, "G": exact_string(data.G),
                "Q": exact_string(quadratic_form(data)),
                "lambda": {str(d): exact_string(data.lam[d]) for d in data.divisors},
            })
    for s in range(1, 13):
        masses = radical_pair_masses(s)
        assert sum(masses.values(), Fraction()) == harmonic(s) ** 2
        counts["radical_group_partitions"] += 1
        for d, mass in masses.items():
            assert mass <= (3 if d % 2 == 0 else 1) * h(d)
            counts["radical_group_bounds"] += 1
        total = sum((h(d) for d in range(1, s * s + 1) if squarefree(d)), Fraction())
        assert harmonic(s) ** 2 <= 3 * total
        counts["harmonic_sieve_bounds"] += 1
    for t in range(9):
        assert harmonic(2 ** t) >= 1 + Fraction(t, 2)
        assert (t + 1) ** 2 <= 2 ** (2 * t)
        counts["dyadic_harmonic_bounds"] += 1
        counts["dyadic_polynomial_bounds"] += 1
    for X in (0, 1, 2, 3, 10, 31, 100):
        for z in range(1, 13):
            data = sieve_data(z)
            square_sum = weighted_square_sum(X, data)
            sifted = sifted_count(X, z)
            assert sifted <= square_sum
            assert abs(square_sum - Fraction(X) / data.G) <= z ** 4
            assert twin_count(X) <= z + sifted
            assert twin_count(X) <= z + Fraction(X) / data.G + z ** 4
            counts["sieve_majorants"] += 1
            counts["sieve_error_bounds"] += 1
            counts["twin_sieve_inclusions"] += 1
            counts["finite_twin_bounds"] += 1
    for N in range(101):
        numerator, denominator = brun_integer_code(N)
        assert Fraction(numerator, denominator) == brun_partial_sum(N)
        counts["integer_rational_codes"] += 1
    assert brun_partial_sum(8) == Fraction(1, 3) + 2 * Fraction(1, 5) + Fraction(1, 7)
    counts["five_double_counting"] += 1
    for k in range(1, 13):
        assert k * k * twin_count(2 ** k) <= 2048 * 2 ** k
        counts["dyadic_count_examples"] += 1
    return {
        "status": "PASS",
        "arithmetic": "Exact integers and fractions.Fraction; no floating point",
        "scope": "Finite diagnostic checks, not a formal proof or a proof by exhaustive cases",
        "counting_conventions": {"T(X)": "p <= X", "B(N)": "p < N; overlapping pairs count 5 twice"},
        "proved_article_constant_C": 2048,
        "symbolic_cauchy_cutoff": "N(q) = 2^(2^(q+13)); not evaluated by this program",
        "checks": dict(counts),
        "total_assertions": sum(counts.values()),
        "selected_exact_sieve_data": selected_weights,
        "small_partial_sums": [
            {"N": N, "B(N)": exact_string(brun_partial_sum(N))}
            for N in (4, 6, 8, 20, 100)
        ],
        "partial_sum_note": "These are exact finite sums, not certified practical approximations to the infinite constant.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the verification report to this path")
    args = parser.parse_args()
    report = verification_report()
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.json:
        args.json.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
