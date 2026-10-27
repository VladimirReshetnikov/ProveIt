#!/usr/bin/env python3
"""Reproduce exact finite checks; write a machine-readable verification record.

Run from any directory:

    python3 path/to/code/verify_mode_network.py

The default output is ../results/mode_verification.json relative to this file.
Use --output PATH to choose another destination.  This verifies finite algebra
identities and a rank codec, not the paper's complete algorithm and not an
asymptotic speedup.  The tests intentionally include Cauchy grid roots, negative
integer evaluation points, genuinely nonzero crossing interactions, invalid
binary rank strings, and a higher-precision case with multiple mode factors.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import unittest

from mode_network import (
    CauchyPacket,
    WeightedTuples,
    bounded_weight_tuples,
    fraction_mod,
    valuation_two,
    verify_fixture,
)


class ArithmeticTests(unittest.TestCase):
    def test_exact_two_adic_reduction(self):
        for precision in range(1, 9):
            modulus = 1 << precision
            for numerator in range(-10, 11):
                for denominator in (1, 3, 5, 7, 9):
                    residue = fraction_mod(Fraction(numerator, denominator), precision)
                    self.assertEqual((residue * denominator - numerator) % modulus, 0)
        with self.assertRaises(ValueError):
            fraction_mod(Fraction(1, 2), 5)

    def test_valuations(self):
        self.assertEqual(valuation_two(0), float("inf"))
        self.assertEqual(valuation_two(Fraction(24, 7)), 3)
        self.assertEqual(valuation_two(Fraction(-9, 16)), -4)
        self.assertEqual(valuation_two(Fraction(3, 5)), 0)


class RankingTests(unittest.TestCase):
    def test_rank_unrank_against_independent_enumeration(self):
        for weights in ((), (1,), (2,), (1, 2), (2, 3), (1, 1, 2), (1, 2, 2, 3)):
            for total in range(9):
                with self.subTest(weights=weights, total=total):
                    brute = sorted(
                        word for word in product(*(range(total // weight + 1) for weight in weights))
                        if sum(weight * exponent for weight, exponent in zip(weights, word)) == total
                    )
                    family = WeightedTuples(weights, total)
                    self.assertEqual(family.count, len(brute))
                    self.assertEqual(list(family), brute)
                    for rank, word in enumerate(brute):
                        self.assertEqual(family.rank(word), rank)
                        self.assertEqual(family.unrank(rank), word)

    def test_invalid_binary_codes_have_no_tuple(self):
        family = WeightedTuples((1, 1), 2)
        self.assertEqual(family.count, 3)
        self.assertEqual(family.bit_length, 2)
        self.assertIsNone(family.decode_bits(3))
        with self.assertRaises(ValueError):
            family.decode_bits(4)
        with self.assertRaises(ValueError):
            family.unrank(3)
        with self.assertRaises(ValueError):
            family.rank((0, 0))

    def test_zero_bit_and_empty_families(self):
        unique = WeightedTuples((), 0)
        self.assertEqual(unique.count, 1)
        self.assertEqual(unique.bit_length, 0)
        self.assertEqual(unique.decode_bits(0), ())
        impossible = WeightedTuples((), 1)
        self.assertEqual(impossible.count, 0)
        self.assertIsNone(impossible.decode_bits(0))

    def test_strict_budget_no_duplicates(self):
        for budget in range(1, 10):
            weights = (1, 2, 3)
            words = list(bounded_weight_tuples(weights, budget))
            brute = {
                word for word in product(range(budget), repeat=3)
                if sum(weight * exponent for weight, exponent in zip(weights, word)) < budget
            }
            self.assertEqual(set(words), brute)
            self.assertEqual(len(words), len(brute))


class CauchyTests(unittest.TestCase):
    def test_canceled_polynomial_at_zero_is_identity(self):
        packet = CauchyPacket(4, 1, 0, 5, 100)
        for row, column in product(range(4), repeat=2):
            self.assertEqual(packet.cauchy_entry(row, column, 0), int(row == column))

    def test_nonzero_grid_roots_are_local(self):
        for node in (-3, -2, -1, 1, 2, 3):
            packet = CauchyPacket(4, node, 0, 5, 100)
            for row, column in product(range(4), repeat=2):
                entry = packet.cauchy_entry(row, column, node)
                if column - row == node:
                    self.assertNotEqual(entry, 0)
                    self.assertEqual(packet.row_group(row), packet.column_group(column))
                else:
                    self.assertEqual(entry, 0)

    def test_crossing_expansion_and_divisibility(self):
        for node, zeta, precision in product((-3, -2, -1, 1, 2, 3), (-1, 0, 1, 2), (3, 4, 5)):
            packet = CauchyPacket(4, node, zeta, precision, 100)
            checks = packet.check_kernel_identity()
            self.assertEqual(checks["crossing_entries_checked"], 8)


FIXTURES = (
    (4, 1, 1, 3, 101),
    (4, 1, 1, 4, 102),
    (4, 1, -1, 5, 103),
    (4, -1, 1, 5, 104),
    (4, 3, 2, 5, 105),
    (4, 2, 1, 5, 106),
    (4, -2, 1, 5, 107),
    (4, 1, 0, 5, 108),
    (4, 1, 1, 7, 109),
    (8, 1, 1, 5, 110),
    (8, 2, 1, 5, 111),
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parent.parent / "results" / "mode_verification.json",
    )
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromModule(__import__(__name__))
    test_result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not test_result.wasSuccessful():
        raise SystemExit(1)

    results = [verify_fixture(*fixture) for fixture in FIXTURES]
    if not any(item["nonzero_crossing_entries"] for item in results):
        raise AssertionError("fixtures failed to exercise crossing interactions")
    if not any(item["invalid_rank_assignments_given_zero"] for item in results):
        raise AssertionError("fixtures failed to exercise invalid binary rank strings")
    if not any(item["maximum_nonzero_mode_degree"] >= 2 for item in results):
        raise AssertionError("fixtures failed to exercise a product of multiple mode factors")

    record = {
        "artifact_kind": "exact_identity_prototype",
        "scope": "One fully occupied Cauchy packet, two groups, integer evaluation points; no SAT solver.",
        "not_verified": [
            "No complete implementation of the source SAT algorithm.",
            "No new asymptotic complexity theorem.",
            "No collision packing, Hermite recovery, or recursion-space bound.",
            "No claim that finite fixtures prove the general algebraic identity.",
        ],
        "source_commit": "42907c9e999cc00d6abe7a50bfc1023250edd1b9",
        "arithmetic": "Python integers and fractions.Fraction; all reductions are exact modulo powers of two.",
        "unit_tests_run": test_result.testsRun,
        "unit_tests_passed": test_result.wasSuccessful(),
        "fixture_count": len(results),
        "all_fixture_identities_passed": all(item["all_equal"] for item in results),
        "total_direct_assignment_pairs": sum(item["direct_bit_pairs"] for item in results),
        "total_feasible_mode_tuples": sum(item["feasible_mode_tuples"] for item in results),
        "total_invalid_rank_strings_zeroed": sum(item["invalid_rank_assignments_given_zero"] for item in results),
        "fixtures": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Verified {len(results)} exact direct/global-mode/rank identities; wrote {args.output}")


if __name__ == "__main__":
    main()
