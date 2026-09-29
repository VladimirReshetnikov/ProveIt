#!/usr/bin/env python3
"""Exact, finite regression checks accompanying article.tex.

These tests do not constitute a proof of an infinite theorem.  All arithmetic
checks use Python integers/Fraction; the article supplies the mathematical
proofs and their hypotheses.  No third-party modules or network are required.

Run: python3 verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction as Q
from pathlib import Path
from typing import Sequence


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def ladder(ratios: Sequence[int]) -> tuple[int, ...]:
    out = [1]
    for ratio in ratios:
        if ratio < 2:
            raise ValueError("Ladder ratios must be integers at least two")
        out.append(out[-1] * ratio)
    return tuple(out)


def valuations(n: int) -> dict[int, int]:
    if n < 1:
        raise ValueError("Only positive integers have this factorization")
    ans: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans


def uniform_moments(width: Q, order: int) -> list[Q]:
    return [Q(0) if k % 2 else width ** k / (2 ** k * (k + 1))
            for k in range(order + 1)]


def digit_moments(count: int, spacing: Q, order: int) -> list[Q]:
    if count < 1:
        raise ValueError("The digit count must be positive")
    points = [spacing * (Q(j) - Q(count - 1, 2)) for j in range(count)]
    return [sum((x ** k for x in points), Q(0)) / count
            for k in range(order + 1)]


def add_independent(x: Sequence[Q], y: Sequence[Q]) -> list[Q]:
    if len(x) != len(y):
        raise ValueError("Moment vectors must have the same length")
    return [sum((math.comb(k, j) * x[j] * y[k - j]
                 for j in range(k + 1)), Q(0)) for k in range(len(x))]


def zero_moments(order: int) -> list[Q]:
    return [Q(1)] + [Q(0)] * order


def test_finite_ladders() -> dict[str, int]:
    ladders = [ladder(r) for r in itertools.product(range(2, 5), repeat=4)]
    comparisons = frequency_checks = 0
    for a in ladders:
        for b in ladders:
            deficit = math.lcm(*(x // math.gcd(x, y) for x, y in zip(a, b)))
            for m in range(1, 13):
                coordinate = all((m * y) % x == 0 for x, y in zip(a, b))
                zero_orders = all(sum((m * y) % x == 0 for x in a) >= k + 1
                                  for k, y in enumerate(b))
                require(coordinate == zero_orders, "Coordinate/zero-order mismatch")
                require(coordinate == (m % deficit == 0), "LCM classification mismatch")
                comparisons += 1
                if coordinate:
                    for n in (1, 2, 3, 5, 12, 30, 60, 120, 360, 720):
                        lhs = sum((m * n) % x == 0 for x in a)
                        rhs = sum(n % y == 0 for y in b)
                        require(lhs >= rhs, "Zero domination failed away from generators")
                        frequency_checks += 1
    return {"ladder_pairs_and_scales": comparisons,
            "additional_zero_order_checks": frequency_checks}


def test_uniform_splitting() -> dict[str, int]:
    checks = tilings = 0
    for count in range(1, 25):
        for width in (Q(1), Q(1, 2), Q(2, 3), Q(7, 11)):
            small = width / count
            summed = add_independent(uniform_moments(small, 12),
                                     digit_moments(count, small, 12))
            target = uniform_moments(width, 12)
            for lhs, rhs in zip(summed, target):
                require(lhs == rhs, "Uniform splitting moment identity failed")
                checks += 1
            intervals = [(small * (Q(j) - Q(count, 2)),
                          small * (Q(j + 1) - Q(count, 2))) for j in range(count)]
            require(intervals[0][0] == -width / 2, "Wrong left endpoint")
            require(intervals[-1][1] == width / 2, "Wrong right endpoint")
            require(all(intervals[j][1] == intervals[j + 1][0]
                        for j in range(count - 1)), "Intervals do not tile")
            tilings += 1
    return {"rational_moment_equalities": checks, "exact_interval_tilings": tilings}


def test_prefix_factorizations() -> dict[str, int]:
    checks = cases = 0
    order = 10
    for a, b in ((2, 2), (2, 4), (2, 6), (3, 3), (3, 6), (4, 8)):
        for m in range(1, 7):
            for last in range(3):
                target = zero_moments(order)
                small = zero_moments(order)
                noise = zero_moments(order)
                for k in range(last + 1):
                    target = add_independent(target, uniform_moments(Q(1, a ** k), order))
                    small = add_independent(small, uniform_moments(Q(1, m * b ** k), order))
                    count = m * (b // a) ** k
                    noise = add_independent(noise, digit_moments(count, Q(1, m * b ** k), order))
                recovered = add_independent(small, noise)
                for lhs, rhs in zip(target, recovered):
                    require(lhs == rhs, "Finite geometric residual identity failed")
                    checks += 1
                cases += 1
    return {"prefix_factorization_cases": cases, "rational_moment_equalities": checks}


def test_boolean_encoding() -> dict[str, int]:
    primes = (3, 5, 7, 11, 13, 17, 19, 23)
    all_sets = [{j for j in range(8) if mask & (1 << j)} for mask in range(256)]
    ladders = [tuple(2 ** k * math.prod(primes[j] for j in s if j < k)
                     for k in range(9)) for s in all_sets]
    checks = 0
    for i, s in enumerate(all_sets):
        for j, t in enumerate(all_sets):
            lcm_value = math.lcm(*(x // math.gcd(x, y)
                                  for x, y in zip(ladders[i], ladders[j])))
            prime_value = math.prod(primes[k] for k in s - t)
            require(lcm_value == prime_value, "Prime-discrepancy formula failed")
            require((lcm_value == 1) == s.issubset(t), "Order orientation failed")
            checks += 1
    return {"ordered_pairs_of_finite_sets": checks}


def test_integer_base_witnesses() -> dict[str, int]:
    positive = negative = 0
    for a in range(2, 21):
        for b in range(2, 21):
            for m in range(1, 21):
                av, bv, mv = valuations(a), valuations(b), valuations(m)
                if b % a == 0:
                    for k in range(13):
                        require((m * b ** k) % (a ** k) == 0, "Allowed base pair failed")
                    positive += 1
                else:
                    p = next(p for p in av if av[p] > bv.get(p, 0))
                    k = mv.get(p, 0) // (av[p] - bv.get(p, 0)) + 1
                    require((m * b ** k) % (a ** k) != 0, "Prime witness did not refute")
                    # Actual analytic zero-order obstruction at t=m*b**k.
                    n = m * b ** k
                    v = 0
                    power = 1
                    while n % power == 0:
                        v += 1
                        power *= a
                    require(v < k + 1, "Multiplicity obstruction did not refute")
                    negative += 1
    return {"allowed_base_scale_triples": positive,
            "forbidden_base_scale_triples_with_explicit_witness": negative}


def test_cocycle() -> dict[str, int]:
    order = 10
    checks = 0
    for m in range(1, 6):
        for n in range(1, 6):
            for a, b, c in ((1, 2, 6), (2, 4, 8), (3, 6, 12)):
                direct = digit_moments(m * n * c // a, Q(1, m * n * c), order)
                first = digit_moments(m * b // a, Q(1, m * b), order)
                second = digit_moments(n * c // b, Q(1, m * n * c), order)
                composed = add_independent(first, second)
                for lhs, rhs in zip(direct, composed):
                    require(lhs == rhs, "Noise cocycle moment identity failed")
                    checks += 1
    return {"rational_moment_equalities": checks}



def test_periodic_ratios() -> dict[str, int]:
    cycles = list(itertools.product(range(2, 6), repeat=2))
    positive = negative = 0
    for ca in cycles:
        for cb in cycles:
            qa, qb = math.prod(ca), math.prod(cb)
            need = ca[0] // math.gcd(ca[0], cb[0])
            for m in range(1, 25):
                expected = qb % qa == 0 and m % need == 0
                aa = ladder(ca * 12)
                bb = ladder(cb * 12)
                require(expected == all((m * y) % x == 0 for x, y in zip(aa, bb)),
                        "Periodic-ratio finite check failed")
                if qb % qa:
                    va, vb, vm = valuations(qa), valuations(qb), valuations(m)
                    prime = next(p for p in va if va[p] > vb.get(p, 0))
                    j = vm.get(prime, 0) // (va[prime] - vb.get(prime, 0)) + 1
                    require((m * qb ** j) % (qa ** j) != 0,
                            "Periodic-ratio slope witness failed")
                elif not expected:
                    require((m * cb[0]) % ca[0] != 0,
                            "Periodic-ratio prefix witness failed")
                if expected:
                    positive += 1
                else:
                    negative += 1
    return {"allowed_periodic_schedule_scale_triples": positive,
            "forbidden_periodic_schedule_scale_triples": negative}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    tests = {
        "finite_ladders": test_finite_ladders(),
        "uniform_splitting": test_uniform_splitting(),
        "prefix_factorizations": test_prefix_factorizations(),
        "boolean_encoding": test_boolean_encoding(),
        "integer_base_witnesses": test_integer_base_witnesses(),
        "cocycle": test_cocycle(),
        "periodic_ratios": test_periodic_ratios(),
    }
    result = {
        "status": "PASS",
        "arithmetic": "Exact Python integers and fractions.Fraction; no floating-point tests",
        "scope": "Finite regression checks, not a formal verification of infinite theorems",
        "tests": tests,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
