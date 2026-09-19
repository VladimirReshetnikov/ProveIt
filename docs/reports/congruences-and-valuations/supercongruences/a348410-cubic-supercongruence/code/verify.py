#!/usr/bin/env python3
"""Exact, standard-library verification accompanying the A348410 research note.

Requires Python 3.9 or later. No network, floating point, or computer algebra
system is used. These finite checks supplement, rather than replace, the proof.
Run from any directory: python code/verify.py
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import comb, isqrt
from pathlib import Path
from typing import Iterator, List, Optional


def require(condition: bool, message: str) -> None:
    """Unlike an assert statement, this remains active under python -O."""
    if not condition:
        raise AssertionError(message)


def divide_exact(numerator: int, denominator: int) -> int:
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError(f"Nonexact division by {denominator}")
    return quotient


def vp(number: int, prime: int) -> Optional[int]:
    """Return the prime valuation; None represents positive infinity at zero."""
    if number == 0:
        return None
    number = abs(number)
    result = 0
    while number % prime == 0:
        number //= prime
        result += 1
    return result


def valuation_at_least(number: int, prime: int, bound: int) -> bool:
    value = vp(number, prime)
    return value is None or value >= bound


def primes_up_to(limit: int) -> List[int]:
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def power_coefficients(u: int, v: int, power: int, degree: int) -> Iterator[int]:
    """Yield [x^j](1-x)^(-u*power)(1+x)^(-v*power), for 0 <= j <= degree.

    The recurrence follows by differentiating the generating function. It uses
    exact integer division, not modular division, even when the divisor is p.
    Only two previous coefficients are retained.
    """
    if power < 0 or degree < 0:
        raise ValueError("power and degree must be nonnegative")
    previous_two, previous = 0, 1
    yield 1
    for j in range(1, degree + 1):
        current = divide_exact(
            power * (u - v) * previous
            + (power * (u + v) + j - 2) * previous_two, j)
        yield current
        previous_two, previous = previous, current


@lru_cache(maxsize=4096)
def diagonal(u: int, v: int, n: int) -> int:
    """A_{u,v}(n), including its declared value 1 at n=0."""
    result = 1
    for result in power_coefficients(u, v, n, n):
        pass
    return result


def negative_binomial_coefficient(exponent: int, degree: int) -> int:
    """Coefficient of x^degree in (1-x)^(-exponent), for integer exponent."""
    if degree < 0:
        return 0
    if exponent > 0:
        return comb(exponent + degree - 1, degree)
    if degree > -exponent:
        return 0
    return (-1) ** degree * comb(-exponent, degree)


def diagonal_by_binomials(u: int, v: int, n: int) -> int:
    return sum(negative_binomial_coefficient(u * n, n - j)
               * negative_binomial_coefficient(v * n, j) * (-1) ** j
               for j in range(n + 1))


def a348410_by_positive_sum(n: int) -> int:
    if n == 0:
        return 1
    return sum(comb(2 * n - 2 * k - 1, n - 2 * k)
               * comb(n + k - 1, k) for k in range(n // 2 + 1))


def a348410_by_baskets(n: int) -> int:
    """Independent repeated convolution of floor(j/2)+1, for small n."""
    values = [1] + [0] * n
    for _ in range(n):
        values = [sum(values[j - k] * (k // 2 + 1)
                      for k in range(j + 1)) for j in range(n + 1)]
    return values[n]


def save_csv(path: Path, rows: list) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def mul(a: List[int], b: List[int], size: int) -> List[int]:
    result = [0] * size
    for i, ai in enumerate(a[:size]):
        for j, bj in enumerate(b[:size - i]):
            result[i + j] += ai * bj
    return result


def add(*terms: List[int]) -> List[int]:
    size = max(map(len, terms))
    return [sum(term[i] if i < len(term) else 0 for term in terms)
            for i in range(size)]


def scale(a: List[int], scalar: int) -> List[int]:
    return [scalar * value for value in a]


def mobius(n: int) -> int:
    result = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            result = -result
            if n % d == 0:
                return 0
        d += 1
    return -result if n > 1 else result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=5000,
                        help="largest index in the extended original-sequence sweep")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    if args.max_n < 100:
        parser.error("--max-n must be at least 100")
    args.output.mkdir(parents=True, exist_ok=True)
    summary = {"python": platform.python_version(), "max_n": args.max_n,
               "arithmetic": "exact integers and rational/modular arithmetic",
               "formal_proof_assistant_check": False}

    # Values quoted in the OEIS entry inspected on 2026-09-19.
    initial = [1, 1, 5, 19, 85, 376, 1715, 7890, 36693, 171820,
               809380, 3830619, 18201235, 86770516, 414836210,
               1988138644, 9548771157, 45948159420, 221470766204,
               1069091485500, 5167705849460, 25009724705460,
               121171296320475, 587662804774890, 2852708925078675,
               13859743127937876]
    for n, value in enumerate(initial):
        require(diagonal(2, 1, n) == value, f"OEIS initial value {n}")
    for n in range(151):
        require(diagonal(2, 1, n) == a348410_by_positive_sum(n),
                f"positive binomial sum, n={n}")
    for n in range(13):
        require(diagonal(2, 1, n) == a348410_by_baskets(n),
                f"basket convolution, n={n}")
    independent = 0
    for u, v in product(range(-3, 5), repeat=2):
        for n in range(26):
            require(diagonal(u, v, n) == diagonal_by_binomials(u, v, n),
                    f"signed binomial convolution {(u, v, n)}")
            independent += 1
    summary.update(initial_oeis_values=len(initial),
                   positive_sum_comparisons=151,
                   basket_convolution_comparisons=13,
                   signed_binomial_comparisons=independent)

    rows = []
    for p in primes_up_to(97):
        if p == 2:
            continue
        power, r = p, 1
        while power <= args.max_n:
            for m in range(1, 6):
                n = m * power
                if n > args.max_n:
                    continue
                delta = diagonal(2, 1, n) - diagonal(2, 1, n // p)
                actual = vp(delta, p)
                target = 3 * (r + int(vp(m, p))) - int(p == 3)
                require(valuation_at_least(delta, p, target),
                        f"original supercongruence {(p, r, m)}")
                rows.append(dict(p=p, r=r, m=m, n=n,
                                 required_valuation=target,
                                 observed_valuation="infinity" if actual is None else actual,
                                 leading_unit_mod_p="" if actual is None
                                 else (delta // (p ** actual)) % p))
            power *= p
            r += 1
    save_csv(args.output / "original_congruences.csv", rows)
    summary["original_supercongruence_tests"] = len(rows)
    summary["largest_original_index_tested"] = max(row["n"] for row in rows)

    family_rows = []
    for u, v in product(range(-3, 5), repeat=2):
        for p, max_r in [(3, 3), (5, 2), (7, 2), (11, 1)]:
            for r in range(1, max_r + 1):
                for m in [1, 2, 3, 5]:
                    n = m * p ** r
                    delta = diagonal(u, v, n) - diagonal(u, v, n // p)
                    bound = 3 * (r + int(vp(m, p))) - int(p == 3)
                    require(valuation_at_least(delta, p, bound),
                            f"two-parameter theorem {(u, v, p, r, m)}")
                    observed = vp(delta, p)
                    family_rows.append(dict(u=u, v=v, p=p, r=r, m=m, n=n,
                                            required_valuation=bound,
                                            observed_valuation="infinity" if observed is None
                                            else observed))
    save_csv(args.output / "family_congruences.csv", family_rows)
    summary["family_supercongruence_tests"] = len(family_rows)

    # Check the key quadratic lemma modulo its stated lower bound.
    quadratic_tests = 0
    for u, v in [(2, 1), (-2, 3), (3, 4), (0, 0), (1, 1)]:
        for p in [3, 5, 7, 11, 13]:
            indices = sorted(set([p * m for m in range(1, 51)] + [p ** 3]))
            for M in indices:
                s = int(vp(M, p))
                modulus = p ** (s - int(p == 3))
                residue = 0
                for i in range(1, M):
                    if i % p:
                        weight = (u + v * (-1) ** i) * (u + v * (-1) ** (M - i))
                        residue += weight * pow(i * (M - i), -1, modulus)
                require(residue % modulus == 0,
                        f"quadratic lemma {(u, v, p, M)}")
                quadratic_tests += 1
    summary["quadratic_coefficient_tests"] = quadratic_tests

    coefficient_tests = 0
    for u, v in [(2, 1), (-2, 3), (3, 4), (0, 0), (1, 1)]:
        for p in [3, 5, 7]:
            for r in [1, 2, 3]:
                L = p ** r
                for j, value in enumerate(power_coefficients(u, v, L, L + 10)):
                    if j:
                        bound = max(0, r - int(vp(j, p)))
                        require(valuation_at_least(value, p, bound),
                                f"derivative coefficient lemma {(u, v, p, r, j)}")
                        coefficient_tests += 1
    summary["derivative_coefficient_tests"] = coefficient_tests

    tail_tests = 0
    for p in primes_up_to(97):
        if p == 2:
            continue
        for r in range(1, 6):
            factorial_valuation = 0
            for k in range(1, 1001):
                factorial_valuation += int(vp(k, p))
                if k >= 3:
                    require(k * r - factorial_valuation >= 3 * r - int(p == 3),
                            f"exponential tail {(p, r, k)}")
                    tail_tests += 1
    summary["exponential_tail_tests"] = tail_tests

    # Independent, finite checks of both parametric and eliminated generating functions.
    size = 61
    a = [diagonal(2, 1, n) for n in range(size)]
    y = [0]
    for n in range(1, size):
        last = 1
        for last in power_coefficients(2, 1, n, n - 1):
            pass
        y.append(divide_exact(last, n))
    y2 = mul(y, y, size)
    y3 = mul(y2, y, size)
    y4 = mul(y2, y2, size)
    require(add(y, scale(y2, -1), scale(y3, -1), y4)
            == [0, 1] + [0] * (size - 2), "inverse defining polynomial")
    denom = add([1] + [0] * (size - 1), scale(y, -1), scale(y2, -4))
    require(mul(denom, a, size) == add([1] + [0] * (size - 1), scale(y2, -1)),
            "parametric ordinary generating function")
    a2 = mul(a, a, size)
    a3 = mul(a2, a, size)
    a4 = mul(a2, a2, size)
    polynomial = add(mul([-32, 107, 256], add(a4, scale(a3, -1)), size),
                     mul([0, 36, 96], a2, size),
                     mul([0, -4, -16], a, size), [0, 0, 1] + [0] * (size - 3))
    require(all(value == 0 for value in polynomial), "quartic ordinary generating function")
    summary["generating_function_coefficients_checked"] = size

    # Boundary examples, including the exact hypotheses of the cited framing claim.
    require(diagonal(2, 1, 5) - diagonal(2, 1, 1) == 375, "sharp p=5 example")
    require(diagonal(2, 1, 3) - diagonal(2, 1, 1) == 18, "sharp p=3 example")
    boundary = []
    for t in [1, 3, 9]:
        d1 = t
        d5 = comb(5 * t + 4, 5) + 5 * t * comb(5 * t + 1, 2)
        require(vp(d5 - d1, 5) == 2, f"period-three boundary t={t}")
        boundary.append(dict(t=t, d1=d1, d5=d5, difference=d5 - d1,
                             residue_mod_125=(d5 - d1) % 125))
    b = lambda j: 3 + 9 * int(j % 3 == 0)
    harmonic = sum(Fraction(b(5 - k) * b(k), k * k) for k in range(1, 5))
    require(harmonic == Fraction(361, 16), "weighted harmonic counterexample")
    require((harmonic.numerator * pow(harmonic.denominator, -1, 5)) % 5 == 1,
            "weighted harmonic residue")
    rational_two_tests = 0
    for p in primes_up_to(97):
        for r in range(1, 5):
            for m in range(1, 101):
                require(valuation_at_least(b(m * p ** r) - b(m * p ** (r - 1)), p, 2 * r),
                        f"rational 2-sequence input {(p, r, m)}")
                rational_two_tests += 1
    save_csv(args.output / "period_three_counterexamples.csv", boundary)
    summary["rational_two_input_tests"] = rational_two_tests
    summary["weighted_harmonic_counterexample"] = str(harmonic)

    primitive = []
    for n in range(1, 101):
        numerator = sum(mobius(n // d) * diagonal(2, 1, d)
                        for d in range(1, n + 1) if n % d == 0)
        value = Fraction(numerator, n ** 3)
        denominator = value.denominator
        for p in primes_up_to(100):
            if p >= 5:
                require(denominator % p != 0, f"Mobius primitive denominator {(n, p)}")
        require(denominator % 9 != 0, f"Mobius primitive at p=3, n={n}")
        if n % 2:
            require((3 * value).denominator == 1, f"odd Mobius primitive n={n}")
        primitive.append(dict(n=n, a_n=diagonal(2, 1, n),
                              primitive_numerator=value.numerator,
                              primitive_denominator=value.denominator))
    save_csv(args.output / "cubic_mobius_transform.csv", primitive)
    save_csv(args.output / "a348410_terms.csv", [dict(n=n, a_n=diagonal(2, 1, n))
                                                for n in range(151)])
    summary["mobius_transform_indices_checked"] = 100
    summary["result"] = "PASS: all finite checks succeeded"
    text = json.dumps(summary, indent=2)
    (args.output / "verification_summary.json").write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, ArithmeticError, ValueError) as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        sys.exit(1)
