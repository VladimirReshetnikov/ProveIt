from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path

from pcog import (
    ContractError,
    RationalInterval,
    all_below,
    any_below,
    backward_viability,
    bounded_chain_fuel,
    build_cubic_graph,
    common_good_index,
    complete_height_list,
    finite_horizon_paths,
    least_below,
    least_viable_path,
    lex_decreases,
    list_height_bound,
    mixed_radix_rank,
    pow2_neg,
    rational_height,
    rational_pairs,
    stable_label,
)


class TestPCOG(unittest.TestCase):
    def test_bounded_booleanization_primitives(self) -> None:
        self.assertTrue(all_below(8, lambda i: i < 8))
        self.assertTrue(any_below(9, lambda i: i * i == 16))
        self.assertEqual(least_below(20, lambda i: i * i >= 30), 6)
        self.assertIsNone(least_below(5, lambda i: i > 10))

    def test_contract_graph_and_backward_demands(self) -> None:
        graph = build_cubic_graph()
        run = graph.run({"observable": 8}, {"x": Fraction(1), "apartness_bits": 0})
        self.assertEqual(run.demands["observable"], 8)
        self.assertEqual(run.demands["reciprocal"], 9)
        self.assertEqual(run.demands["root"], 13)
        root = run.outputs["root"]
        obs = run.outputs["observable"]
        self.assertIsInstance(root, RationalInterval)
        self.assertIsInstance(obs, RationalInterval)
        self.assertLessEqual(root.width, pow2_neg(13))
        self.assertLessEqual(obs.width, pow2_neg(8))
        # The positive root of y^3+y=1 lies between 1/2 and 1.
        self.assertLessEqual(Fraction(1, 2), root.hi)
        self.assertGreater(root.lo, 0)

    def test_guarded_inverse_refuses_zero(self) -> None:
        graph = build_cubic_graph()
        with self.assertRaises(ContractError):
            graph.run({"observable": 4}, {"x": Fraction(0), "apartness_bits": 0})

    def test_uniform_cubic_apartness_demand(self) -> None:
        graph = build_cubic_graph()
        for a in range(7):
            lower = pow2_neg(a)
            samples = (lower, (lower + 2) / 2, Fraction(2))
            for q in range(9):
                for x in samples:
                    run = graph.run(
                        {"observable": q},
                        {"x": x, "apartness_bits": a},
                    )
                    self.assertEqual(run.demands["reciprocal"], q + 1)
                    self.assertEqual(run.demands["root"], q + 2 * a + 5)
                    self.assertLessEqual(
                        run.outputs["reciprocal"].width, pow2_neg(q + 1)
                    )
                    self.assertLessEqual(
                        run.outputs["observable"].width, pow2_neg(q)
                    )

    def test_backward_viability_and_least_path(self) -> None:
        clouds = (
            (0, 2),
            (0, 1, 3),
            (1, 2, 4),
            (2, 5),
        )
        compatible = lambda _level, a, b: abs(a - b) <= 1
        viable = backward_viability(clouds, compatible)
        self.assertEqual(viable[0], (True, True))
        result = least_viable_path(clouds, compatible)
        self.assertEqual(result.path, (0, 0, 0, 0))
        paths = finite_horizon_paths(clouds, compatible)
        self.assertEqual(tuple(len(p) for p in paths), (1, 2, 3, 4))

    def test_no_relational_path_is_explicit(self) -> None:
        clouds = ((0,), (2,))
        with self.assertRaises(ContractError):
            least_viable_path(clouds, lambda _level, a, b: abs(a - b) <= 1)

    def test_gap_collapse(self) -> None:
        labels = [Fraction(-1), Fraction(1), Fraction(4)]
        interval = RationalInterval(Fraction(9, 10), Fraction(11, 10))
        self.assertEqual(stable_label(interval, labels, Fraction(3, 2)), Fraction(1))
        with self.assertRaises(ContractError):
            stable_label(RationalInterval(Fraction(-1), Fraction(1)), labels, Fraction(3, 2))

    def test_finite_union_window(self) -> None:
        bad = [lambda i: i in {0, 2}, lambda i: i in {1, 3, 5}]
        witness = common_good_index(7, bad, [2, 3])
        self.assertIn(witness, {4, 6})

    def test_height_list_equivalence_direction(self) -> None:
        universe = rational_pairs(5)
        solutions = complete_height_list(
            5,
            universe,
            rational_height,
            lambda q: q * q == 1,
        )
        self.assertEqual(solutions, (Fraction(-1), Fraction(1)))
        self.assertEqual(list_height_bound(solutions, rational_height), 1)

    def test_mixed_radix_descent(self) -> None:
        bounds = (3, 4, 2)
        before = (2, 0, 2)
        after = (1, 4, 2)
        self.assertTrue(lex_decreases(before, after, bounds))
        self.assertLess(mixed_radix_rank(after, bounds), mixed_radix_rank(before, bounds))
        self.assertEqual(bounded_chain_fuel(bounds), 4 * 5 * 3)


if __name__ == "__main__":
    unittest.main(verbosity=2)
