#!/usr/bin/env python3
"""Verify exact schedules against independent rational Hermite recovery.

Run with Python 3.10+; no third-party packages are required.  The default JSON
record is ../results/precision_verification.json relative to this script.

The checks construct Hermite multipliers directly from their products over
integer nodes.  They do not use the proposed finite-loss formula to construct
those multipliers.  Integer and rational Cauchy-product polynomials are
recovered from complete jets and from jets reduced at the proposed precisions.
Controlled error injections test the precision boundary, including a one-bit
reduction which can change the answer.  These are finite implementation checks,
not substitutes for the general proof in the accompanying note.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import comb, prod
from pathlib import Path
from random import Random
import subprocess
import sys
import unittest

from precision_schedule import (
    SOURCE_COMMIT,
    ceiling,
    finite_loss_numerators,
    finite_optimal,
    from_taper,
    full_normalized_losses,
    optimized_linear,
    rounded_optimal_full,
    source_linear,
    weighted_multiplicity,
)


STRATEGIES = (source_linear, optimized_linear, rounded_optimal_full, finite_optimal)


def v2(value: int | Fraction) -> int | float:
    """Independent valuation helper used only by the verification script."""
    value = Fraction(value)
    if not value:
        return float("inf")
    numerator, denominator = abs(value.numerator), value.denominator
    result = 0
    while numerator % 2 == 0:
        numerator //= 2
        result += 1
    while denominator % 2 == 0:
        denominator //= 2
        result -= 1
    return result


def reduce_fraction(value: int | Fraction, precision: int) -> int:
    value = Fraction(value)
    if value.denominator % 2 == 0:
        raise AssertionError("attempted to reduce a nonintegral two-adic value")
    modulus = 1 << precision
    return value.numerator * pow(value.denominator, -1, modulus) % modulus


def multiply_polynomials(left, right, order=None):
    if order is None:
        order = len(left) + len(right) - 1
    result = [Fraction(0)] * order
    for i, a in enumerate(left[:order]):
        for j, b in enumerate(right[:order - i]):
            result[i + j] += a * b
    return result


def cauchy_polynomial(length: int, row: int, column: int):
    grid = range(-length, length)
    denominator = prod(-node for node in grid if node)
    polynomial = [Fraction(1)]
    for node in grid:
        if node != column - row:
            polynomial = multiply_polynomials(polynomial, [-node, 1])
    return [coefficient / denominator for coefficient in polynomial]


def random_polynomial(schedule, kind: str, seed: int):
    rng = Random(seed)
    if kind == "integer":
        return [Fraction(rng.randint(-4, 4)) for _ in range(schedule.degree_bound + 1)]
    if kind != "rational-cauchy-product":
        raise ValueError("unknown polynomial fixture kind")
    result = [Fraction(rng.randint(1, 5))] + [Fraction(0)] * schedule.degree_bound
    for term in range(3):
        polynomial = [Fraction(rng.choice((-3, -2, -1, 1, 2, 3)))]
        for factor in range(schedule.wires):
            row = rng.randrange(schedule.packet_length)
            # Include both diagonal and off-diagonal factors.
            column = row if (factor + term) % 2 else rng.randrange(schedule.packet_length)
            polynomial = multiply_polynomials(
                polynomial, cauchy_polynomial(schedule.packet_length, row, column))
        for index, coefficient in enumerate(polynomial):
            result[index] += coefficient
    return result


class HermitePlan:
    """Independent exact product-form Hermite evaluator on the source grid."""

    def __init__(self, schedule):
        self.schedule = schedule
        self.alpha = 2 * schedule.packet_length
        self.nodes = tuple(
            node for node in range(-schedule.packet_length, schedule.packet_length)
            if node and v2(node) < schedule.levels
            and schedule.multiplicities[int(v2(node))]
        )
        self.orders = {node: schedule.multiplicities[int(v2(node))] for node in self.nodes}
        self.origin_multipliers = {}
        self.reciprocal_series = {}
        for node in self.nodes:
            order = self.orders[node]
            origin = Fraction(1)
            inverse = [Fraction(1)] + [Fraction(0)] * (order - 1)
            for other in self.nodes:
                if other == node:
                    continue
                multiplicity = self.orders[other]
                origin *= Fraction(-other, node - other) ** multiplicity
                ratio = Fraction(self.alpha, node - other)
                # (1+ratio*z)^(-multiplicity), truncated to this node's jet.
                factor = [(-1) ** j * comb(multiplicity + j - 1, j) * ratio ** j
                          for j in range(order)]
                inverse = multiply_polynomials(inverse, factor, order)
            self.origin_multipliers[node] = origin
            self.reciprocal_series[node] = inverse

    def jets(self, coefficients):
        result = {}
        for node in self.nodes:
            order = self.orders[node]
            result[node] = [
                sum((coefficients[k] * comb(k, j) * node ** (k - j) * self.alpha ** j
                     for k in range(j, len(coefficients))), Fraction(0))
                for j in range(order)
            ]
        return result

    def recover(self, jets):
        result = Fraction(0)
        for node in self.nodes:
            order = self.orders[node]
            quotient = multiply_polynomials(jets[node], self.reciprocal_series[node], order)
            argument = Fraction(-node, self.alpha)
            value = Fraction(0)
            for coefficient in reversed(quotient):
                value = coefficient + argument * value
            result += self.origin_multipliers[node] * value
        return result


class ScheduleTests(unittest.TestCase):
    def test_invalid_parameters_and_tapers(self):
        for parameters in ((0, 1, 1, 1), (1, 1, 2, 1), (1, 2, 2, 1),
                           (1, 2, 0, 1), (1, 2, 1, 0), (1.5, 2, 1, 1)):
            with self.subTest(parameters=parameters):
                with self.assertRaises(ValueError):
                    optimized_linear(*parameters)
        with self.assertRaises(ValueError):
            from_taper(2, 2, 2, 3, (1, 3))
        with self.assertRaises(ValueError):
            from_taper(2, 2, 2, 3, (0, 0))
        with self.assertRaises(ValueError):
            from_taper(2, 2, 2, 3, (4, 0), working_precisions=(1, None))

    def test_minimum_linear_slope(self):
        for exponent in range(1, 13):
            for levels in range(1, exponent + 1):
                for wires in (levels, levels + 1, 2 * levels + 1, 100 * levels):
                    schedule = optimized_linear(wires, exponent, levels, 7)
                    slope = schedule.multiplicities[-1]
                    denominator = sum((1 << (exponent - i)) * (levels - i) for i in range(levels))
                    self.assertGreater(slope * denominator, schedule.degree_bound)
                    self.assertLessEqual((slope - 1) * denominator, schedule.degree_bound)
                    closed_denominator = (1 << exponent) * (
                        2 * levels - 2 + Fraction(2, 1 << levels))
                    self.assertEqual(denominator, closed_denominator)

    def test_all_profiles_are_complete_monotone_and_sufficient(self):
        for exponent in range(1, 11):
            for levels in range(1, exponent + 1):
                for wires in (levels, 2 * levels + 1, 37 * levels):
                    for constructor in STRATEGIES:
                        schedule = constructor(wires, exponent, levels, 5)
                        self.assertGreater(schedule.total_multiplicity, schedule.degree_bound)
                        self.assertTrue(all(a >= b for a, b in zip(schedule.multiplicities, schedule.multiplicities[1:])))
                        self.assertTrue(all(value >= 0 for value in schedule.losses))
                        self.assertTrue(all(actual >= needed for actual, needed in
                                            zip(schedule.working_precisions, schedule.exact_sufficient_precisions)))

    def test_real_optima_and_rounding_error(self):
        for exponent in range(1, 11):
            for levels in range(1, exponent + 1):
                full = rounded_optimal_full(17 * levels, exponent, levels, 5)
                finite = finite_optimal(17 * levels, exponent, levels, 5)
                for schedule in (full, finite):
                    required = Fraction(schedule.degree_bound + 1, schedule.packet_length)
                    self.assertEqual(weighted_multiplicity(schedule.real_multiplicities), required)
                    self.assertEqual(tuple(ceiling(value) for value in schedule.real_multiplicities), schedule.multiplicities)
                self.assertEqual(set(full_normalized_losses(full.real_multiplicities)),
                                 {full.real_optimal_normalized_loss})
                finite_real_losses = finite_loss_numerators(exponent, finite.real_multiplicities)
                finite_normalized = {loss / (1 << (exponent - i)) for i, loss in enumerate(finite_real_losses)}
                self.assertEqual(finite_normalized, {finite.real_optimal_normalized_loss})
                self.assertLessEqual(finite.real_optimal_normalized_loss, full.real_optimal_normalized_loss)
                for loss in full_normalized_losses(full.multiplicities):
                    self.assertLess(loss, full.real_optimal_normalized_loss + 2)
                for loss in finite.normalized_losses:
                    self.assertLess(loss, finite.real_optimal_normalized_loss + 2)

    def test_source_formula_and_inactive_level(self):
        source = source_linear(1000, 12, 6, 1001)
        self.assertEqual(source.multiplicities, (3000, 2500, 2000, 1500, 1000, 500))
        self.assertEqual(source.working_precisions[0], 1001 + 8 * 500 * 4096 + 8 * 1000 * 13)
        custom = from_taper(2, 2, 2, 3, (4, 0))
        self.assertIsNone(custom.working_precisions[1])

    def test_independent_audit_implementation_agrees(self):
        from verify_bounds import equal_loss_profile, finite_losses, infinite_losses, weighted_mass
        for levels in range(1, 13):
            for exponent in (levels, levels + 1, 2 * levels):
                for constructor in STRATEGIES:
                    schedule = constructor(31 * levels, exponent, levels, 5)
                    q = schedule.multiplicities
                    self.assertEqual(weighted_multiplicity(q), weighted_mass(q))
                    self.assertEqual(full_normalized_losses(q), infinite_losses(q))
                    self.assertEqual(schedule.normalized_losses, finite_losses(q, exponent))
                full = rounded_optimal_full(31 * levels, exponent, levels, 5)
                self.assertEqual(tuple(value / full.real_optimal_normalized_loss
                                       for value in full.real_multiplicities),
                                 equal_loss_profile(levels))

    def test_command_line_strategies_emit_exact_json(self):
        module = Path(__file__).resolve().with_name("precision_schedule.py")
        for strategy in ("linear", "equal-loss", "finite-optimal"):
            completed = subprocess.run(
                [sys.executable, str(module), "--wires", "1000", "--packet-exponent", "12",
                 "--levels", "6", "--input-precision", "1001", "--strategy", strategy],
                check=True, capture_output=True, text=True,
            )
            data = json.loads(completed.stdout)
            self.assertEqual(data["selected"]["strategy"], strategy)
            self.assertGreaterEqual(data["selected"]["total_multiplicity"],
                                    data["selected"]["required_total_multiplicity"])


def verify_recovery_fixture(schedule, polynomial_kind, seed):
    plan = HermitePlan(schedule)
    coefficients = random_polynomial(schedule, polynomial_kind, seed)
    jets = plan.jets(coefficients)
    exact = plan.recover(jets)
    if exact != coefficients[0]:
        raise AssertionError("exact Hermite recovery failed")

    rng = Random(seed + 10000)
    reduced = {}
    perturbed = {}
    boundary_checks = 0
    for node in plan.nodes:
        level = int(v2(node))
        if v2(plan.origin_multipliers[node]) != -schedule.losses[level]:
            raise AssertionError("finite-loss formula disagrees with direct multiplier product")
        required = schedule.exact_sufficient_precisions[level]
        working = schedule.working_precisions[level]
        assert required is not None and working is not None
        for coefficient in jets[node]:
            if v2(coefficient) < 0:
                raise AssertionError("fixture violates the source's local integrality premise")
        reduced[node] = [Fraction(reduce_fraction(coefficient, working)) for coefficient in jets[node]]
        perturbed[node] = [coefficient + rng.choice((-3, -1, 1, 3)) * (1 << required)
                           for coefficient in jets[node]]

        # Alter only the highest quotient jet.  The reciprocal has constant
        # one, so altering the highest F-jet has exactly this recovery effect.
        multiplier = (plan.origin_multipliers[node]
                      * Fraction(-node, plan.alpha) ** (plan.orders[node] - 1))
        safe_error = multiplier * (1 << required)
        unsafe_error = multiplier * (1 << (required - 1))
        if v2(safe_error) != schedule.input_precision:
            raise AssertionError("exact precision boundary was not attained")
        if reduce_fraction(safe_error, schedule.input_precision) != 0:
            raise AssertionError("full-budget error did not disappear")
        if reduce_fraction(unsafe_error, schedule.input_precision) == 0:
            raise AssertionError("one-bit smaller precision unexpectedly preserved all errors")
        boundary_checks += 1

    target = reduce_fraction(coefficients[0], schedule.input_precision)
    if reduce_fraction(plan.recover(reduced), schedule.input_precision) != target:
        raise AssertionError("recovery from working-precision residues failed")
    if reduce_fraction(plan.recover(perturbed), schedule.input_precision) != target:
        raise AssertionError("independent allowed coefficient errors changed the answer")

    # Also test the boundary by a full recovery, not only its derived multiplier.
    node = plan.nodes[0]
    level = int(v2(node))
    required = schedule.exact_sufficient_precisions[level]
    boundary_jets = {key: list(value) for key, value in jets.items()}
    boundary_jets[node][-1] += 1 << (required - 1)
    recovered_bad = plan.recover(boundary_jets)
    if reduce_fraction(recovered_bad, schedule.input_precision) == target:
        raise AssertionError("full recovery did not detect the deliberately one-bit-too-large error")

    return {
        "strategy": schedule.strategy,
        "wires": schedule.wires,
        "packet_exponent": schedule.packet_exponent,
        "levels": schedule.levels,
        "input_precision": schedule.input_precision,
        "polynomial_kind": polynomial_kind,
        "seed": seed,
        "polynomial_degree_bound": schedule.degree_bound,
        "rational_coefficients_present": any(coefficient.denominator != 1 for coefficient in coefficients),
        "active_node_count": len(plan.nodes),
        "retained_jet_coefficient_count": sum(plan.orders.values()),
        "exact_rational_recovery_passed": True,
        "working_precision_recovery_passed": True,
        "simultaneous_allowed_error_injection_passed": True,
        "multiplier_valuation_checks": len(plan.nodes),
        "exact_boundary_checks": boundary_checks,
        "one_bit_less_can_change_answer": True,
        "recovered_residue": target,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent / "results" / "precision_verification.json")
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ScheduleTests)
    tests = unittest.TextTestRunner(verbosity=2).run(suite)
    if not tests.wasSuccessful():
        raise SystemExit(1)
    parameters = ((1, 1, 1, 3), (1, 2, 1, 4), (2, 2, 2, 3), (2, 3, 2, 4), (3, 3, 3, 5))
    fixtures = []
    for parameter_index, parameter in enumerate(parameters):
        for constructor in STRATEGIES:
            schedule = constructor(*parameter)
            for kind in ("integer", "rational-cauchy-product"):
                fixtures.append(verify_recovery_fixture(schedule, kind, 700 + parameter_index))
    if not any(fixture["rational_coefficients_present"] for fixture in fixtures):
        raise AssertionError("fixtures did not exercise genuinely rational polynomial coefficients")

    examples = [{"parameters": {"wires": wires, "packet_exponent": exponent,
                                "levels": levels, "input_precision": precision},
                 "schedules": [constructor(wires, exponent, levels, precision).as_dict()
                               for constructor in STRATEGIES]}
                for wires, exponent, levels, precision in ((1000, 12, 6, 1001), (1000000, 40, 20, 1000001))]
    record = {
        "artifact_kind": "exact_hermite_schedule_verification",
        "source_commit": SOURCE_COMMIT,
        "scope": "Finite exact tests of multiplicity and precision refinement; not a full SAT solver or a running-time benchmark.",
        "unit_tests_run": tests.testsRun,
        "unit_tests_passed": tests.wasSuccessful(),
        "independent_reference_crosscheck": "verify_bounds.py: weighted_mass, finite_losses, infinite_losses, equal_loss_profile",
        "recovery_fixture_count": len(fixtures),
        "all_recovery_fixtures_passed": True,
        "total_exact_boundary_checks": sum(item["exact_boundary_checks"] for item in fixtures),
        "total_direct_multiplier_valuation_checks": sum(item["multiplier_valuation_checks"] for item in fixtures),
        "fixtures": fixtures,
        "example_schedules": examples,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Verified {len(fixtures)} exact Hermite recovery fixtures; wrote {args.output}")


if __name__ == "__main__":
    main()
