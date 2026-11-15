#!/usr/bin/env python3
"""Exact trace checks for elliptic E1 and nontrivial parity descent on Z^r."""

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
from elliptic import EllipticCurve, point_text
from coordinates import (coordinate_vector, coordinates, extract_coordinates,
                         generator_list, linear_combination, reconstruct,
                         result_metadata)
from symbolic_resultant import symbolic_duplication_resultant


def lattice_example(initial):
    dimension = len(initial)
    representatives = [tuple((mask >> i) & 1 for i in range(dimension))
                       for mask in range(1 << dimension)]
    height = lambda point: sum(x * x for x in point)
    add = lambda p, q: tuple(x + y for x, y in zip(p, q))
    mul = lambda n, p: tuple(n * x for x in p)
    zero = (0,) * dimension

    def split(p):
        index = sum((x % 2) << i for i, x in enumerate(p))
        return index, tuple(x // 2 for x in p)

    result = extract_coordinates(initial, representatives, dimension, height,
                                 split, add, mul, zero)
    return result, (add, mul, zero)


LATTICE_INPUTS = [(1000,), (-999,), (1000, -999), (47, -28, 69),
                  (12, -300, 50, 7), (0, 0), (1, -1, 0)]


class CoordinateChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.curve = EllipticCurve(-1, 0)
        cls.representatives = cls.curve.enumerate_points(1)
        cls.generators = generator_list(cls.curve, cls.representatives)

    def test_e1_coordinates(self):
        self.assertEqual(len(self.generators), 8)
        for p in self.representatives:
            result = coordinates(self.curve, self.representatives, p)
            self.assertTrue(result.success)
            self.assertEqual(result.threshold, 12)
            self.assertEqual(result.active_steps, 0)
            self.assertEqual(reconstruct(result, self.curve.add, self.curve.mul, None), p)
            vector = coordinate_vector(self.curve, self.representatives, result, self.generators)
            self.assertEqual(linear_combination(vector, self.generators,
                                                self.curve.add, self.curve.mul, None), p)

    def test_nontrivial_lattice_descent(self):
        active_total = 0
        frozen_total = 0
        for initial in LATTICE_INPUTS:
            result, (add, mul, zero) = lattice_example(initial)
            self.assertTrue(result.success)
            self.assertEqual(reconstruct(result, add, mul, zero), initial)
            self.assertLessEqual(sum(x * x for x in result.terminal), len(initial))
            self.assertEqual(len(result.trace), result.fuel)
            self.assertLessEqual(result.active_steps, result.fuel)
            self.assertLessEqual(result.terminal_coefficient, result.coefficient_bound)
            self.assertTrue(all(0 <= a <= result.coefficient_bound
                                for a in result.representative_coefficients))
            self.assertEqual(result.terminal_coefficient, 1 << result.active_steps)
            for j, row in enumerate(result.trace, start=1):
                self.assertLessEqual(max(row.height_after - result.threshold, 0),
                                     result.initial_excess // (1 << j))
                if row.kind == "active":
                    active_total += 1
                    self.assertLess(row.height_after, row.height_before)
                    self.assertEqual(add(mul(2, row.after), result.representatives[row.selected_index]),
                                     row.before)
                if row.kind == "frozen":
                    frozen_total += 1
                    self.assertEqual(row.before, row.after)
        self.assertGreater(active_total, 20)
        self.assertGreater(frozen_total, 0)

    def test_missing_decomposition_is_reported(self):
        result = extract_coordinates(100, [0], 0, abs,
                                     lambda p: (0, p // 2) if p % 2 == 0 else None,
                                     lambda p, q: p + q, lambda n, p: n * p, 0)
        self.assertFalse(result.success)
        self.assertIn("No supplied representative", result.failure_reason)
        self.assertEqual(result.terminal, 25)
        self.assertEqual(result.terminal_coefficient, 4)
        self.assertEqual(reconstruct(result, lambda p, q: p + q,
                                     lambda n, p: n * p, 0), 100)

    def test_bad_contract_is_rejected(self):
        bad_equation = extract_coordinates(10, [0], 0, abs, lambda p: (0, p),
                                           lambda p, q: p + q, lambda n, p: n * p, 0)
        self.assertFalse(bad_equation.success)
        self.assertIn("group equation", bad_equation.failure_reason)

    def test_symbolic_resultant(self):
        report = symbolic_duplication_resultant()
        self.assertTrue(report["verified"])
        self.assertEqual(report["permutations_checked"], 40320)


def write_metadata(result):
    curve = EllipticCurve(-1, 0)
    representatives = curve.enumerate_points(1)
    generators = CoordinateChecks.generators
    elliptic = []
    for p in representatives:
        data = coordinates(curve, representatives, p)
        row = result_metadata(data, point_text)
        row["full_coordinate_vector"] = coordinate_vector(curve, representatives, data, generators)
        elliptic.append(row)
    failure = extract_coordinates(100, [0], 0, abs,
                                  lambda p: (0, p // 2) if p % 2 == 0 else None,
                                  lambda p, q: p + q, lambda n, p: n * p, 0)
    report = {
        "tests_run": result.testsRun, "failures": len(result.failures),
        "errors": len(result.errors), "successful": result.wasSuccessful(),
        "fuel": "bit_length(max(h(P)-C,0))",
        "coefficient_bound": "2*max(1,h(P)-C)",
        "E1": {"C": 12, "bounded_generator_search_height": 4096,
               "generators_with_duplicates": [point_text(p) for p in generators],
               "representations": elliptic},
        "lattice_fixture": {"height": "sum of coordinate squares", "threshold": "dimension r",
                            "representatives": "all vectors in {0,1}^r",
                            "step": "coordinatewise parity digit and floor division by two",
                            "identity": "2*sum(q_i^2) <= sum((2*q_i+d_i)^2)+r for d_i in {0,1}",
                            "runs": [result_metadata(lattice_example(p)[0], list) for p in LATTICE_INPUTS]},
        "missing_decomposition_example": result_metadata(failure, int),
        "symbolic_resultant": symbolic_duplication_resultant(),
        "logical_limits": [
            "The elliptic extractor assumes the universal covering property of the supplied representatives.",
            "A successful individual trace certifies only its own expansion and displayed height checks.",
            "The E1 global classification is proved by the report's Fermat descent, not by finite enumeration alone.",
            "The Z^r fixtures exercise active and frozen steps of the same generic extraction code.",
            "Exact symbolic determinant expansion verifies a polynomial identity by coefficient computation; it is not an embedded Lean proof."
        ],
    }
    path = ROOT / "metadata" / "coordinate_checks.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return path


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CoordinateChecks)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print("Metadata:", write_metadata(result))
    raise SystemExit(0 if result.wasSuccessful() else 1)
