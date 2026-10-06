#!/usr/bin/env python3
"""Exact finite verification of the uniformity discrepancy inequalities.

All arithmetic is integral or rational.  No floating point roots or tolerance
comparisons are used.  The program is a finite check of examples, not a proof
of the general theorems proved in the article.

Run from any directory with Python 3.  The default output is the neighboring
uniformity_results.json file.  Only the Python standard library is required.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
import itertools
import json
from math import factorial, gcd
from pathlib import Path


def progression_count(values: tuple[int, ...], length: int) -> int:
    modulus = len(values)
    return sum(
        all(values[(base + index * difference) % modulus]
            for index in range(length))
        for base in range(modulus)
        for difference in range(modulus)
    )


def integer_cube_moment(values: tuple[int, ...], degree: int) -> int:
    """Unnormalized sum_h |sum_x Delta_h^(degree-1) values(x)|^2."""
    if degree == 1:
        return sum(values) ** 2
    modulus = len(values)
    return sum(
        integer_cube_moment(
            tuple(values[x] * values[(x + shift) % modulus]
                  for x in range(modulus)),
            degree - 1,
        )
        for shift in range(modulus)
    )


@lru_cache(maxsize=None)
def balanced_uniformity_energy(
    values: tuple[int, ...], degree: int
) -> Fraction:
    """Return ||1_A - |A|/N||_{U^degree}^{2^degree} exactly."""
    modulus = len(values)
    cardinality = sum(values)
    scaled_balanced = tuple(modulus * value - cardinality for value in values)
    numerator = integer_cube_moment(scaled_balanced, degree)
    denominator = modulus ** (degree + 1 + 2 ** degree)
    return Fraction(numerator, denominator)


def rational_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def verify_set(values: tuple[int, ...], length: int) -> dict:
    modulus = len(values)
    assert gcd(modulus, factorial(length - 1)) == 1
    density = Fraction(sum(values), modulus)
    count = progression_count(values, length)
    discrepancy = abs(Fraction(count, modulus * modulus) - density ** length)
    energy = balanced_uniformity_energy(values, length - 1)
    power = 2 ** (length - 1)
    linear_coefficient = sum(
        (density ** index for index in range(length - 2)), Fraction(0)
    )
    quadratic_coefficient = sum(
        ((index + 1) * density ** index for index in range(length - 2)),
        Fraction(0),
    )

    # |error| <= S epsilon, raised to power 2^(k-1).
    linear_lhs = discrepancy ** power
    linear_rhs = linear_coefficient ** power * energy
    assert linear_lhs <= linear_rhs

    # |error| <= sqrt(delta) B epsilon^2, raised to power 2^(k-2).
    # This exponent is even for k>=3, so every quantity stays rational.
    quadratic_lhs = discrepancy ** (power // 2)
    quadratic_rhs = (
        density ** (power // 4)
        * quadratic_coefficient ** (power // 2)
        * energy
    )
    assert quadratic_lhs <= quadratic_rhs

    sharper_three_term_equal = False
    if length == 3:
        variance_rhs = density * (1 - density) * energy
        assert discrepancy ** 2 <= variance_rhs
        sharper_three_term_equal = discrepancy ** 2 == variance_rhs

    # Directly verify the exact diagonal count and properness of every d!=0
    # progression in the ambient group.
    constant_count = sum(values)
    nonconstant_count = sum(
        all(values[(base + index * difference) % modulus]
            for index in range(length))
        for base in range(modulus)
        for difference in range(1, modulus)
    )
    assert count == nonconstant_count + constant_count
    assert all(
        len({(index * difference) % modulus for index in range(length)})
        == length
        for difference in range(1, modulus)
    )

    # Equivalent rational form of the displayed convenient alpha criterion:
    # energy <= (delta^(k-1/2)/(2B))^(2^(k-2)).
    alpha_threshold = (
        density ** ((2 * length - 1) * (power // 4))
        / (2 * quadratic_coefficient) ** (power // 2)
    )
    threshold_fires = (
        density > 0
        and modulus > 2 * density ** (1 - length)
        and energy <= alpha_threshold
    )
    if threshold_fires:
        assert nonconstant_count > 0

    return {
        "N": modulus,
        "k": length,
        "mask": sum(value << index for index, value in enumerate(values)),
        "cardinality": sum(values),
        "progressions": count,
        "nonconstant_progressions": nonconstant_count,
        "energy": rational_text(energy),
        "discrepancy": rational_text(discrepancy),
        "linear_equality": linear_lhs == linear_rhs,
        "quadratic_equality": quadratic_lhs == quadratic_rhs,
        "three_term_variance_equality": sharper_three_term_equal,
        "existence_threshold_fires": threshold_fires,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("uniformity_results.json"),
    )
    options = parser.parse_args()

    records = []
    batches = []
    for modulus, lengths in ((5, (3, 4, 5)), (7, (3, 4))):
        initial = len(records)
        for mask in range(1 << modulus):
            values = tuple((mask >> index) & 1 for index in range(modulus))
            for length in lengths:
                records.append(verify_set(values, length))
        batches.append({
            "group": f"Z/{modulus}Z",
            "lengths": list(lengths),
            "scope": "all subsets",
            "subsets": 1 << modulus,
            "set_length_pairs": len(records) - initial,
        })

    modulus = 25
    quadratic_residues = {(index * index) % modulus for index in range(modulus)}
    composite_sets = (
        ("empty", set()),
        ("full", set(range(modulus))),
        ("singleton", {0}),
        ("multiples_of_five", set(range(0, modulus, 5))),
        ("interval_of_nine", set(range(9))),
        ("even_representatives", set(range(0, modulus, 2))),
        ("quadratic_residues", quadratic_residues),
        ("deterministic_sample", {
            index for index in range(modulus)
            if ((17 * index * index + 11 * index + 3) % 29) < 13
        }),
    )
    initial = len(records)
    for name, subset in composite_sets:
        values = tuple(int(index in subset) for index in range(modulus))
        for length in (3, 4):
            record = verify_set(values, length)
            record["sample_name"] = name
            records.append(record)
    batches.append({
        "group": "Z/25Z",
        "lengths": [3, 4],
        "scope": "eight explicitly specified subsets",
        "subsets": len(composite_sets),
        "set_length_pairs": len(records) - initial,
    })

    # The k=2 formula is checked separately for every subset above.
    two_term_pairs = 0
    for modulus in (5, 7):
        for mask in range(1 << modulus):
            values = tuple((mask >> index) & 1 for index in range(modulus))
            cardinality = sum(values)
            assert progression_count(values, 2) == cardinality ** 2
            assert progression_count(values, 2) - cardinality == (
                cardinality * (cardinality - 1)
            )
            two_term_pairs += 1

    payload = {
        "status": "all exact checks passed",
        "arithmetic": "Python integers and fractions.Fraction; no floating roots",
        "scope": "finite examples; the article contains the general proofs",
        "batches": batches,
        "set_length_pairs": len(records),
        "two_term_cases": two_term_pairs,
        "linear_bounds_checked": len(records),
        "quadratic_bounds_checked": len(records),
        "sharp_three_term_bounds_checked": sum(r["k"] == 3 for r in records),
        "sharp_three_term_equalities": sum(
            r["three_term_variance_equality"] for r in records if r["k"] == 3
        ),
        "existence_threshold_successes": sum(
            r["existence_threshold_fires"] for r in records
        ),
        "records_sha256": hashlib.sha256(
            json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "records": records,
    }
    options.output.parent.mkdir(parents=True, exist_ok=True)
    options.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in payload.items()
                      if key != "records"}, indent=2))


if __name__ == "__main__":
    main()
