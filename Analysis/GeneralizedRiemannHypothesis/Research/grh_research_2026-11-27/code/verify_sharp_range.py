#!/usr/bin/env python3
"""Independent exact checks for the sharp p-adic staircase.

Uses finite-field jets, not sparse_disk.py and not floating point.
The witness check expands the final integer polynomial at X=1 directly.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb, gcd, lcm
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parents[1]


def digit_sum(n: int, p: int) -> int:
    answer = 0
    while n:
        answer += n % p
        n //= p
    return answer


def valuation(n: int, p: int):
    if n == 0:
        return None
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer


def weak_compositions(n: int, slots: int):
    if slots == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for tail in weak_compositions(n - first, slots - 1):
            yield (first,) + tail


def jet_rank_rule(profile: tuple[int, ...], p: int):
    """Exact near-boundary rule in the range sum(profile)<=2p-1.

    Formula for the staircase is deliberately not used here.
    The finite candidate set follows only from digit compression at p^2.
    """
    t = sum(profile)
    candidates = set(range(t))
    candidates.update(
        i + p * j + p * p * k
        for i in range(p - 1)
        for j in range(p - 1 - i)
        for k in range(p - 1 - i - j)
    )
    candidates = sorted(candidates, key=lambda k: (digit_sum(k, p), k))
    coordinates = [(a, j) for a, m in enumerate(profile) for j in range(m)]
    echelon = {}
    chosen = []
    for k in candidates:
        vector = [
            comb(k, j) * pow(a, k - j, p) % p if j <= k else 0
            for a, j in coordinates
        ]
        for pivot in sorted(echelon):
            if vector[pivot]:
                factor = vector[pivot]
                vector = [
                    (x - factor * y) % p
                    for x, y in zip(vector, echelon[pivot])
                ]
        pivot = next((i for i, x in enumerate(vector) if x), None)
        if pivot is None:
            continue
        inverse = pow(vector[pivot], -1, p)
        echelon[pivot] = [x * inverse % p for x in vector]
        chosen.append(k)
        if len(echelon) == t:
            break
    assert len(echelon) == t
    return max([t - 1] + chosen), chosen


def expected_bound(p: int, t: int) -> int:
    return p * p + (t - p - 2) // 2


def explicit_functional(k: int, p: int, d: int, a: int) -> int:
    derivative = (
        comb(k, d - 1) * pow(a, k - d + 1, p) % p if k >= d - 1 else 0
    )
    return (
        derivative
        - int(k == d - 1)
        - d * a * int(k == d)
        - a * int(k == p + d - 1)
    ) % p


def multiply_linear(poly: list[int], root: int) -> list[int]:
    result = [0] * (len(poly) + 1)
    for i, c in enumerate(poly):
        result[i] -= root * c
        result[i + 1] += c
    return result


def rational_witness(p: int, d: int):
    exponents = sorted(
        [j * p for j in range(p + d)] + [1 + j * p for j in range(d)]
    )
    moments = [explicit_functional(k, p, d, 1) for k in range(len(exponents))]
    coefficients = []
    for n in exponents:
        cardinal = [1]
        denominator = 1
        for m in exponents:
            if m == n:
                continue
            cardinal = multiply_linear(cardinal, m)
            denominator *= n - m
        coefficients.append(
            Fraction(sum(c * x for c, x in zip(cardinal, moments)), denominator)
        )
    common_denominator = lcm(*(x.denominator for x in coefficients))
    integers = [int(x * common_denominator) for x in coefficients]
    common_numerator = gcd(*integers)
    integers = [x // common_numerator for x in integers]
    return exponents, integers


def binomial_certificate(exponents, coefficients, p: int, depth: Fraction):
    degree = max(exponents)
    expansion = [
        sum(c * comb(n, k) for n, c in zip(exponents, coefficients) if n >= k)
        for k in range(degree + 1)
    ]
    values = [valuation(c, p) for c in expansion]
    weights = [
        None if v is None else Fraction(v) + k * depth
        for k, v in enumerate(values)
    ]
    minimum = min(w for w in weights if w is not None)
    minima = [k for k, w in enumerate(weights) if w == minimum]
    return {
        "expansion_at_one": expansion,
        "valuations": values,
        "weights": [None if w is None else str(w) for w in weights],
        "minimum": str(minimum),
        "minimizing_indices": minima,
        "root_count": max(minima),
    }


def integer_eisenstein_witness(p=5, d=2):
    exponents, coefficients = rational_witness(p, d)
    count = p * p + d - 1
    depth = Fraction(1, p - 1) + Fraction(1, 2 * (p - 1) * count)
    original = binomial_certificate(exponents, coefficients, p, depth)
    assert original["root_count"] == count
    height = int(Fraction(original["minimum"])) + 3
    power = p**height
    final = []
    for n, c in zip(exponents, coefficients):
        modulus = 4 if n == 0 else 2
        residue = 2 if n == 0 else int(n == max(exponents))
        correction = (residue - c) * pow(power, -1, modulus) % modulus
        updated = c + power * correction
        if updated == 0:
            updated += power * modulus
        final.append(updated)
    assert all(final)
    assert final[-1] % 2 == 1
    assert final[0] % 4 == 2
    assert all(c % 2 == 0 for c in final[:-1])
    checked = binomial_certificate(exponents, final, p, depth)
    assert checked["root_count"] == count
    assert all((a - b) % power == 0 for a, b in zip(final, coefficients))
    return {
        "prime": p,
        "terms": len(exponents),
        "exponents": exponents,
        "coefficients": final,
        "depth": str(depth),
        "root_count": count,
        "eisenstein_prime": 2,
        "perturbation_modulus": power,
        "newton_certificate": checked,
    }


def main():
    results = {"method": "exact finite-field jets and integer binomial expansion"}
    exhaustive = []
    for t in range(7, 10):
        seen = 0
        maximum = 0
        maximizers = 0
        for profile in weak_compositions(t, 5):
            actual, _ = jet_rank_rule(profile, 5)
            assert actual <= expected_bound(5, t), (profile, actual)
            if max(profile) > 5 and sum(m > 0 for m in profile) > 1:
                m = max(profile)
                q = max(x for x in profile if x != m)
                assert actual == 25 + min(m - 5, q) - 1
            maximum = max(maximum, actual)
            maximizers += actual == expected_bound(5, t)
            seen += 1
        assert maximum == expected_bound(5, t)
        exhaustive.append({"p": 5, "t": t, "profiles": seen,
                           "maximum": maximum, "maximizers": maximizers})
    results["exhaustive"] = exhaustive

    endpoints = []
    for p in [3, 5, 7, 11, 13, 17]:
        for t in range(p + 2, 2 * p):
            d = (t - p) // 2
            profile = (p + d, d + (t - p) % 2) + (0,) * (p - 2)
            actual, chosen = jet_rank_rule(profile, p)
            assert actual == expected_bound(p, t)
            endpoints.append({"p": p, "t": t, "profile": profile,
                              "maximum": actual, "independent_indices": chosen})
    results["attaining_profiles"] = endpoints

    random_generator = random.Random(20261127)
    random_cases = 0
    for p in [5, 7, 11, 13]:
        for _ in range(100):
            t = random_generator.randrange(p + 2, 2 * p)
            if random_cases % 2 == 0:
                m = random_generator.randrange(p + 1, t)
                profile = [m] + [0] * (p - 1)
                for _ in range(t - m):
                    profile[random_generator.randrange(1, p)] += 1
            else:
                profile = [0] * p
                for _ in range(t):
                    profile[random_generator.randrange(p)] += 1
            actual, _ = jet_rank_rule(tuple(profile), p)
            assert actual <= expected_bound(p, t)
            if max(profile) > p and sum(m > 0 for m in profile) > 1:
                m = max(profile)
                q = max(x for x in profile if x != m)
                assert actual == p * p + min(m - p, q) - 1
            random_cases += 1
    results["seeded_profiles_checked"] = random_cases

    functional_cases = 0
    for p in [3, 5, 7, 11, 13]:
        for d in range(1, (p - 1) // 2 + 1):
            target = p * p + d - 1
            for a in range(1, p):
                for k in range(p**3 + p + 1):
                    ds = digit_sum(k, p)
                    value = explicit_functional(k, p, d, a)
                    if ds < d or (ds == d and k < target):
                        assert value == 0, (p, d, a, k)
                    if k == target:
                        assert value == a
                    functional_cases += 1
    results["functional_evaluations_checked"] = functional_cases

    witness = integer_eisenstein_witness()
    results["integer_witness"] = {
        "p": witness["prime"], "terms": witness["terms"],
        "depth": witness["depth"], "root_count": witness["root_count"],
        "irreducibility_certificate": "Eisenstein at 2",
        "detail_file": "sharp_range_witness.json",
    }
    destination = ROOT / "results"
    destination.mkdir(exist_ok=True)
    (destination / "sharp_range_verification.json").write_text(
        json.dumps(results, indent=2) + "\n"
    )
    (destination / "sharp_range_witness.json").write_text(
        json.dumps(witness, indent=2) + "\n"
    )
    print(json.dumps({
        "exhaustive_profiles": sum(x["profiles"] for x in exhaustive),
        "attaining_profiles": len(endpoints),
        "seeded_profiles": random_cases,
        "functional_evaluations": functional_cases,
        "witness_root_count": witness["root_count"],
        "status": "all exact checks passed",
    }, indent=2))


if __name__ == "__main__":
    main()
