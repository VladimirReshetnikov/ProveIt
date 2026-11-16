#!/usr/bin/env python3
from __future__ import annotations

import unittest
from fractions import Fraction

from reference_framework import (
    LayeredRelation,
    all_below,
    any_below,
    demo_results,
    enumerate_bounded,
    finite_sum_trace,
    least_below,
    maximum_height,
    sqrt2_relation,
    verify_shrinking_bound,
)


class BooleanFoldTests(unittest.TestCase):
    def test_all_any_and_least(self) -> None:
        self.assertTrue(all_below(7, lambda i: i < 7))
        self.assertFalse(all_below(7, lambda i: i != 4))
        self.assertTrue(any_below(10, lambda i: i * i == 49))
        self.assertFalse(any_below(7, lambda i: i == 8))
        self.assertEqual(least_below(20, lambda i: i * i >= 30), 6)
        self.assertEqual(least_below(5, lambda i: i == 9), 5)


class TraceTests(unittest.TestCase):
    def test_finite_sum_reflection_instance(self) -> None:
        values = [4, -8, 15, 16, 23, 42]
        trace = finite_sum_trace(values)
        self.assertTrue(trace.local_obligations_hold(0))
        self.assertTrue(trace.reflected_result(0))
        self.assertEqual(trace.run(0)[-1], sum(values))


class ViabilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.rel = LayeredRelation[int, int](
            candidates=lambda k: {0: [0, 1], 1: [0, 1], 2: [0]}.get(k, []),
            good=lambda _k, _a: True,
            compat=lambda k, a, b: (
                (k == 0 and ((a, b) in {(0, 0), (1, 1)}))
                or (k == 1 and (a, b) == (1, 0))
            ),
            observation=lambda _k, a: a,
        )

    def test_backward_viability_removes_dead_end(self) -> None:
        back = self.rel.backward_viable(2)
        self.assertEqual(back[2], {0})
        self.assertEqual(back[1], {1})
        self.assertEqual(back[0], {1})

    def test_path_equivalence_and_selector(self) -> None:
        self.assertFalse(self.rel.viable_from(0, 2, 0))
        self.assertTrue(self.rel.viable_from(0, 2, 1))
        self.assertEqual(self.rel.least_path_from(0, 2, 1), (1, 1, 0))
        self.assertTrue(self.rel.path_ok((1, 1, 0)))

    def test_full_viability_and_path_through(self) -> None:
        full = self.rel.full_viable(2)
        self.assertEqual(full, {0: {1}, 1: {1}, 2: {0}})
        self.assertEqual(self.rel.least_path_through(2, 1, 1), (1, 1, 0))


class ShrinkingTests(unittest.TestCase):
    def test_sqrt2_clouds_and_bound(self) -> None:
        result = verify_shrinking_bound(
            relation=sqrt2_relation(),
            horizon=lambda k: k + 3,
            epsilon=lambda k: Fraction(1, 2**k),
            delta=lambda k: 3 * Fraction(1, 2**k),
            max_level=8,
        )
        self.assertEqual(result["levels"], 9)
        self.assertEqual(result["pair_checks"], 45)
        self.assertTrue(all(size > 0 for size in result["cloud_sizes"]))


class HeightListTests(unittest.TestCase):
    def test_bound_list_round_trip_example(self) -> None:
        points = enumerate_bounded(range(-25, 26), lambda x: x * x == 16)
        self.assertEqual(set(points), {-4, 4})
        self.assertEqual(maximum_height(points, abs), 4)


class IntegrationTests(unittest.TestCase):
    def test_demo(self) -> None:
        result = demo_results()
        self.assertEqual(result["status"], "all exact finite checks passed")


if __name__ == "__main__":
    unittest.main(verbosity=2)
