#!/usr/bin/env python3
"""Run exact, deterministic checks. No external packages or network needed.

These are finite tests, NOT a proof of a transfinite theorem. The two birthday
implementations share ordinal arithmetic and the same classical sign theorem;
their agreement is a consistency check, not independent formal verification.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys
import time

from ordinal_series import (
    Ordinal, ZERO, ONE, OMEGA, add, birthday_blocks, birthday_endpoint,
    dyadic_birthday, dyadic_signs, multiply, normalize, predicted_equality,
    birthday_product_fast,
    support_bound,
)


def series_family(indices, coefficients, maximum_support):
    yield {}
    for length in range(1, maximum_support + 1):
        for support in combinations(indices, length):
            for values in product(coefficients, repeat=length):
                yield dict(zip(support, values))


def run(seed: int, random_pairs: int) -> dict:
    start = time.perf_counter()
    counts = {}
    # Cross-check dyadic birthdays against an explicit finite sign algorithm.
    count = 0
    for k in range(9):
        for numerator in range(-128, 129):
            c = Fraction(numerator, 2**k)
            assert dyadic_birthday(c) == len(dyadic_signs(c)), c
            count += 1
    counts["dyadic_sign_checks"] = count

    indices = [ZERO, ONE, Ordinal.finite(2), Ordinal.finite(4), OMEGA,
               Ordinal((1, 1)), Ordinal((3, 1)), Ordinal((0, 2)),
               Ordinal((0, 0, 1)), Ordinal((2, 1, 1))]
    for a in indices:
        for b in indices:
            if a <= b:
                assert a.ordinary_add(a.interval_to(b)) == b
    counts["ordinal_interval_checks"] = len(indices) * (len(indices) + 1) // 2
    assert ONE.ordinary_add(OMEGA) == OMEGA
    assert OMEGA.ordinary_add(ONE) == Ordinal((1, 1))
    assert OMEGA.natural_add(ONE) == Ordinal((1, 1))

    coefficients = list(map(Fraction, [-2, -1, Fraction(-1, 2), Fraction(1, 3),
                                      Fraction(1, 2), 1, Fraction(3, 2), 2]))
    count = 0
    for series in series_family(indices, coefficients, 3):
        assert birthday_endpoint(series) == birthday_blocks(series), series
        count += 1
    counts["exhaustive_endpoint_checks"] = count
    print(f"Endpoint/block agreement: {count:,} series", flush=True)

    def check_pair(x, y, bx=None, by=None):
        bx = birthday_endpoint(x) if bx is None else bx
        by = birthday_endpoint(y) if by is None else by
        xy = multiply(x, y)
        bp = birthday_endpoint(xy)
        assert bp == birthday_blocks(xy), (x, y, "blocks")
        assert bp == birthday_product_fast(x, y), (x, y, "four-coefficient formula")
        bound = bx.natural_multiply(by)
        assert bp <= bound, (x, y, "main bound")
        assert (bp == bound) == predicted_equality(x, y), (x, y, "equality")
        assert bp <= support_bound(x, y), (x, y, "support bound")
        assert birthday_endpoint(add(x, y)) <= bx.natural_add(by), (x, y, "sum")
        if x and y:
            assert xy, (x, y, "domain")
            assert bp.degree <= max(bx.degree, by.degree), (x, y, "degree")
            if bx >= OMEGA and by >= OMEGA:
                assert bp < Ordinal.omega_power(max(bx.degree, by.degree) + 1)
                assert bp < bound

    small_coeffs = list(map(Fraction, [-1, Fraction(-1, 2), Fraction(1, 3),
                                      Fraction(1, 2), 1, 2]))
    family = list(series_family([ZERO, ONE, Ordinal.finite(2), OMEGA,
                                 Ordinal((1, 1))], small_coeffs, 2))
    birthdays = list(map(birthday_endpoint, family))
    count = 0
    for i, x in enumerate(family):
        for j in range(i, len(family)):
            check_pair(x, family[j], birthdays[i], birthdays[j])
            count += 1
    counts["exhaustive_product_pairs_unordered_with_repetition"] = count
    counts["exhaustive_product_family_size"] = len(family)
    print(f"Exhaustive products: {count:,} pairs", flush=True)

    rng = random.Random(seed)
    large_indices = sorted(set(indices + [
        Ordinal(tuple(rng.randrange(4) for _ in range(rng.randrange(1, 7))))
        for _ in range(50)
    ]))
    large_coeffs = list({Fraction(n, d) for d in (1, 2, 3, 4, 5, 6, 8)
                        for n in range(-5, 6) if n})
    large_coeffs.sort()
    for _ in range(random_pairs):
        x = {a: rng.choice(large_coeffs)
             for a in rng.sample(large_indices, rng.randrange(0, 7))}
        y = {a: rng.choice(large_coeffs)
             for a in rng.sample(large_indices, rng.randrange(0, 7))}
        check_pair(x, y)
    counts["random_product_pairs"] = random_pairs
    counts["random_index_pool_size"] = len(large_indices)
    counts["four_coefficient_product_checks"] = (
        counts["exhaustive_product_pairs_unordered_with_repetition"] + random_pairs)
    print(f"Random products: {random_pairs:,} pairs", flush=True)

    examples = [
        ("epsilon", {ONE: Fraction(1)}, OMEGA),
        ("3 epsilon^2", {Ordinal.finite(2): Fraction(3)}, Ordinal((2, 2))),
        ("(1/3) epsilon^2", {Ordinal.finite(2): Fraction(1, 3)}, Ordinal((0, 3))),
        ("1 + epsilon", {ZERO: Fraction(1), ONE: Fraction(1)}, OMEGA),
        ("1/3 + epsilon", {ZERO: Fraction(1, 3), ONE: Fraction(1)}, Ordinal((1, 1))),
        ("omega^(-omega)", {OMEGA: Fraction(1)}, Ordinal((0, 0, 1))),
        ("3*(1/3 + epsilon)", {ZERO: Fraction(1), ONE: Fraction(3)}, Ordinal((2, 1))),
    ]
    example_results = []
    for label, x, expected in examples:
        assert birthday_endpoint(x) == expected, label
        example_results.append({"series": label, "birthday": expected.as_text()})
    counts["named_finite_support_examples"] = len(examples)

    return {
        "status": "PASS",
        "seed": seed,
        "python_version": sys.version.split()[0],
        "elapsed_seconds": round(time.perf_counter() - start, 3),
        "counts": counts,
        "examples": example_results,
        "scope": "Finite supports, indices below omega^omega, exact rational coefficients",
        "limitations": [
            "No transfinite support was executed.",
            "No general-surreal multiplication or canonicalization was executed.",
            "Both birthday evaluators use the same classical reduced-sign theorem.",
            "Agreement of tests is not a proof or a novelty certification.",
        ],
    }


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O: verification requires assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260920)
    parser.add_argument("--random-pairs", type=int, default=20000)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "verification.json")
    args = parser.parse_args()
    if args.random_pairs < 0:
        parser.error("--random-pairs must be nonnegative")
    results = run(args.seed, args.random_pairs)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
