#!/usr/bin/env python3
"""Exact finite checks accompanying Exponential Relations over Omnific Integers.

This is NOT an implementation of surreal exponentiation or a complete decision
procedure. Exponentials are basis symbols in a finite formal group algebra.
The tests validate balanced partitions and coordinate arithmetic, not the
imported Lindemann-Weierstrass or Gonshor theorems.

Run with Python 3.10+ (standard library only):
    python3 code/checks.py --output check_results.json
"""
from __future__ import annotations

import argparse
import json
import random
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Hashable, Sequence


@dataclass(frozen=True)
class Q2:
    """Exact a + b*sqrt(2), with rational coordinates."""
    a: Fraction = Fraction(0)
    b: Fraction = Fraction(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", Fraction(self.a))
        object.__setattr__(self, "b", Fraction(self.b))

    @staticmethod
    def coerce(value: Q2 | int | Fraction) -> Q2:
        if isinstance(value, Q2):
            return value
        if isinstance(value, (int, Fraction)):
            return Q2(Fraction(value))
        raise TypeError("Q2 arithmetic accepts only Q2, int, or Fraction")

    def __add__(self, other: Q2 | int | Fraction) -> Q2:
        q = self.coerce(other)
        return Q2(self.a + q.a, self.b + q.b)

    __radd__ = __add__

    def __neg__(self) -> Q2:
        return Q2(-self.a, -self.b)

    def __sub__(self, other: Q2 | int | Fraction) -> Q2:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Q2 | int | Fraction) -> Q2:
        return self.coerce(other) - self

    def __mul__(self, other: Q2 | int | Fraction) -> Q2:
        q = self.coerce(other)
        return Q2(self.a * q.a + 2 * self.b * q.b,
                  self.a * q.b + self.b * q.a)

    __rmul__ = __mul__

    def __truediv__(self, other: Q2 | int | Fraction) -> Q2:
        q = self.coerce(other)
        denominator = q.a * q.a - 2 * q.b * q.b
        if not denominator:
            raise ZeroDivisionError("division by zero in Q(sqrt(2))")
        return self * Q2(q.a / denominator, -q.b / denominator)

    def __bool__(self) -> bool:
        return bool(self.a or self.b)

    def is_integer(self) -> bool:
        return not self.b and self.a.denominator == 1


Partition = tuple[tuple[int, ...], ...]
Coefficient = int | Fraction | Q2


@lru_cache(maxsize=None)
def partitions(n: int) -> tuple[Partition, ...]:
    """All set partitions, uniquely enumerated in restricted-growth order.

    A conservative size cap avoids accidentally allocating a huge Bell family.
    """
    if not isinstance(n, int) or not 0 <= n <= 10:
        raise ValueError("this finite prototype requires 0 <= n <= 10")
    if n == 0:
        return ((),)
    answer = []
    for previous in partitions(n - 1):
        answer.append(previous + ((n - 1,),))
        for block_index in range(len(previous)):
            current = list(previous)
            current[block_index] += (n - 1,)
            answer.append(tuple(current))
    return tuple(answer)


def balanced_partitions(coefficients: Sequence[Coefficient]) -> tuple[Partition, ...]:
    """Return every partition with coefficient sum zero on each block."""
    return tuple(p for p in partitions(len(coefficients))
                 if all(not sum(coefficients[j] for j in block) for block in p))


def partition_zero(coefficients: Sequence[Coefficient],
                   exponents: Sequence[Hashable]) -> bool:
    """Evaluate the balanced-partition disjunction using exact exponent labels."""
    if len(coefficients) != len(exponents):
        raise ValueError("coefficient and exponent lengths differ")
    return any(all(all(exponents[j] == exponents[block[0]] for j in block)
                   for block in p) for p in balanced_partitions(coefficients))


def grouped_zero(coefficients: Sequence[Coefficient],
                 exponents: Sequence[Hashable]) -> bool:
    """Independent oracle: collect equal basis labels directly."""
    if len(coefficients) != len(exponents):
        raise ValueError("coefficient and exponent lengths differ")
    groups: dict[Hashable, Coefficient] = {}
    for coefficient, exponent in zip(coefficients, exponents):
        groups[exponent] = groups.get(exponent, 0) + coefficient
    return all(not value for value in groups.values())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def run_checks() -> dict:
    counts: dict[str, int] = {}
    # Includes n=0: the empty partition and empty exponential sum.
    count = 0
    for n in range(5):
        for coefficients in product((-1, 0, 1), repeat=n):
            balanced = balanced_partitions(coefficients)
            for labels in product(range(3), repeat=n):
                via_partitions = any(
                    all(all(labels[j] == labels[block[0]] for j in block)
                        for block in p) for p in balanced)
                require(via_partitions == grouped_zero(coefficients, labels),
                        f"partition mismatch: {coefficients}, {labels}")
                count += 1
    counts["exhaustive_partition_cases"] = count
    require([len(partitions(n)) for n in range(7)] == [1, 1, 2, 5, 15, 52, 203],
            "incorrect Bell numbers through n=6")

    # A label (n,a,b) represents n + a*omega + b*omega^2. Only additive
    # exponent identities are used; no numerical exponential is evaluated.
    values = tuple(product((-1, 0, 1), repeat=3))
    zero = (0, 0, 0)
    count_sum = count_factor = 0
    for x, y in product(values, repeat=2):
        require(partition_zero((1, 1, -2), (x, y, zero)) == (x == y == zero),
                "exp(x)+exp(y)=2 example failed")
        count_sum += 1
        x_plus_y = tuple(a + b for a, b in zip(x, y))
        require(partition_zero((1, -1, -1, 1), (x_plus_y, x, y, zero))
                == (x == zero or y == zero), "factorization example failed")
        count_factor += 1
    counts["sum_equal_two_cases"] = count_sum
    counts["factorization_cases"] = count_factor

    small_values = tuple(product((-1, 0, 1), repeat=2))
    count = 0
    for x, y, u, v in product(small_values, repeat=4):
        require(partition_zero((1, 1, -1, -1), (x, y, u, v))
                == (Counter((x, y)) == Counter((u, v))), "multiset test failed")
        count += 1
    counts["two_term_multiset_cases"] = count

    sqrt2 = Q2(0, 1)
    count = 0
    for n, a in product(range(-3, 4), repeat=2):
        # The only possible witness is sqrt(2)*(n+a*omega).
        finite = sqrt2 * n
        pure = sqrt2 * a
        require(finite.is_integer() == (n == 0), "pure-part detector failed")
        require((pure / sqrt2) == Q2(a), "quadratic scalar arithmetic failed")
        count += 1
    counts["sqrt2_detector_cases"] = count

    # Exact algebraic coordinate splitting, balanced between true and false
    # equations. The formal basis is (1, omega, omega^2), each with Q2 coefficients.
    rng = random.Random(20260923)
    def qrandom() -> Q2:
        return Q2(Fraction(rng.randint(-3, 3), rng.randint(1, 3)),
                  Fraction(rng.randint(-3, 3), rng.randint(1, 3)))

    true_cases = 0
    for case in range(2000):
        alpha = [qrandom(), qrandom(), qrandom()]
        if not alpha[2]:
            alpha[2] = Q2(1)
        ns = [rng.randint(-4, 4) for _ in range(3)]
        pure = [[qrandom(), qrandom()] for _ in range(3)]
        for coordinate in range(2):
            pure[2][coordinate] = -(alpha[0] * pure[0][coordinate]
                                    + alpha[1] * pure[1][coordinate]) / alpha[2]
        shift = -sum(alpha[k] * ns[k] for k in range(3))
        if case % 2:
            shift += 1
        vectors = [[Q2(ns[k]), *pure[k]] for k in range(3)]
        direct = [sum(alpha[k] * vectors[k][h] for k in range(3))
                  for h in range(3)]
        direct[0] += shift
        direct_zero = all(not value for value in direct)
        ordinary_a = sum(alpha[k].a * ns[k] for k in range(3)) + shift.a
        ordinary_b = sum(alpha[k].b * ns[k] for k in range(3)) + shift.b
        pure_zero = all(not sum(alpha[k] * pure[k][h] for k in range(3))
                        for h in range(2))
        split_zero = not ordinary_a and not ordinary_b and pure_zero
        require(direct_zero == split_zero, "algebraic coordinate split failed")
        require(direct_zero == (case % 2 == 0), "constructed case has wrong sign")
        true_cases += direct_zero
    counts["quadratic_coordinate_split_cases"] = 2000
    counts["quadratic_coordinate_split_true_cases"] = true_cases

    # Real-fiber sign-pattern tests, using rational representatives for the
    # ordinary positive coefficients. Labels are the pure exponential arguments,
    # AFTER multiplication by the base logarithms.
    count = 0
    for a, b in product(range(1, 5), repeat=2):
        for c in (a + b, a + b + 1):
            for p, q, r in product(range(-2, 3), repeat=3):
                require(grouped_zero((a, b, -c), (p, q, r))
                        == (p == q == r and a + b == c), "homogeneous fiber failed")
                count += 1
    counts["homogeneous_fiber_cases"] = count
    count = 0
    for a, b in product(range(1, 6), repeat=2):
        for p, q in product(range(-2, 3), repeat=2):
            require(grouped_zero((a, -b, -1), (p, q, 0))
                    == (p == q == 0 and a - b == 1), "anchored fiber failed")
            count += 1
    counts["anchored_fiber_cases"] = count

    primary_count_keys = [k for k in counts if k != "quadratic_coordinate_split_true_cases"]
    return {
        "status": "PASS",
        "seed": 20260923,
        "total_cases": sum(counts[k] for k in primary_count_keys),
        "counts": counts,
        "bell_numbers_n_0_through_6": [len(partitions(n)) for n in range(7)],
        "limitations": [
            "Formal group algebra, not numerical or actual surreal exponentiation.",
            "No independent proof of Gonshor or Lindemann-Weierstrass.",
            "Not an implementation of the full Presburger/vector QE pipeline.",
            "Not a Lean proof or a verification of proper-class assertions."
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("check_results.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
