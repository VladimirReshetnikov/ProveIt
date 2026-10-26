#!/usr/bin/env python3
"""Finite independent checks of the proposed closed-form cyclic normalization.

This script is experimental evidence, not a proof.  It compares the geometric
sum formula against monotone iteration and, for smaller instances, every
bounded fixed point.  It never imports or executes repository/archived code.
"""
from itertools import product
from pathlib import Path
import argparse
import json


def positive_remainder_carries(radix, raw):
    n = len(raw)
    modulus = radix ** n - 1
    sums = [sum(radix ** (n - 1 - j) * raw[(i - j) % n]
                for j in range(n)) for i in range(n)]
    lower = [max(s - 1, 0) // modulus for s in sums]
    upper = [s // modulus for s in sums]
    return modulus, sums, lower, upper


def step(radix, raw, carries):
    return [(raw[i] + carries[(i - 1) % len(raw)]) // radix
            for i in range(len(raw))]


def iterate_from_zero(radix, raw, bound):
    carries = [0] * len(raw)
    for _ in range(len(raw) * bound + 2):
        new = step(radix, raw, carries)
        assert all(x <= y <= bound for x, y in zip(carries, new))
        if new == carries:
            return carries
        carries = new
    raise AssertionError("Monotone finite iteration exceeded its height bound")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent.parent /
                        'evidence' / 'cyclic_carry_checks.json')
    args = parser.parse_args()
    normalized_cases = 0
    enumerated_fixed_point_instances = 0
    nonzero_residue_instances = 0
    for radix in range(2, 6):
        for n in range(1, 5):
            for bound in range(3):
                max_raw = (bound + 1) * (radix - 1)
                for raw in product(range(max_raw + 1), repeat=n):
                    modulus, sums, lower, upper = positive_remainder_carries(radix, raw)
                    assert all(radix * sums[i] == sums[(i - 1) % n] + modulus * raw[i]
                               for i in range(n))
                    assert step(radix, raw, lower) == lower
                    assert step(radix, raw, upper) == upper
                    assert all(0 <= x <= bound for x in lower)
                    assert lower == iterate_from_zero(radix, raw, bound)
                    digits = [raw[i] + lower[(i - 1) % n] - radix * lower[i]
                              for i in range(n)]
                    assert all(0 <= x < radix for x in digits)
                    residue_nonzero = sums[0] % modulus != 0
                    assert all((s % modulus != 0) == residue_nonzero for s in sums)
                    if residue_nonzero:
                        nonzero_residue_instances += 1
                        assert lower == upper
                    elif any(raw):
                        assert all(u == l + 1 for u, l in zip(upper, lower))
                        assert digits == [radix - 1] * n
                    normalized_cases += 1
                    if n <= 3 and radix <= 4:
                        actual = {carry for carry in product(range(bound + 2), repeat=n)
                                  if step(radix, raw, carry) == list(carry)}
                        expected = {tuple(lower), tuple(upper)}
                        assert actual == expected
                        enumerated_fixed_point_instances += 1
    result = {
        "status": "passed",
        "evidence_kind": "finite Python checks, not a Lean or general mathematical proof",
        "radix_range": [2, 5], "length_range": [1, 4], "carry_budget_range": [0, 2],
        "normalization_instances": normalized_cases,
        "nonzero_residue_instances": nonzero_residue_instances,
        "instances_with_every_bounded_fixed_point_enumerated": enumerated_fixed_point_instances,
        "ambiguity_example": {"radix": 3, "raw": [2, 2],
                              "least_carries": [0, 0], "greatest_carries": [1, 1],
                              "least_digits": [2, 2], "greatest_digits": [0, 0]},
        "square_congruence_counterexample": {
            "modulus": 8, "a": 1, "b": 3,
            "equal_squares_modulus": 1, "a_not_congruent_to_plus_or_minus_b": True}
    }
    assert 1**2 % 8 == 3**2 % 8
    assert 1 % 8 not in (3 % 8, (-3) % 8)
    output = args.output
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
