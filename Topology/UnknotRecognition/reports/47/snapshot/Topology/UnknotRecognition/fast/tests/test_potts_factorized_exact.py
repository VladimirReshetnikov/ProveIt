"""Exact component tensors against independent monolithic and spin sums."""
import itertools
import random
import unittest

from fastunknot.diagram import Diagram
from fastunknot.filters import FilterLimit, PRIME
from fastunknot.potts import POTTS_X
from fastunknot.potts_exact import potts_exact
from fastunknot.potts_factorized import factorized_partition
from fastunknot.potts_factorized_exact import (factorized_exact_partition,
                                              factorized_potts_exact,
                                              factorized_potts_exact_obstruction)
from test_potts import random_knots


def brute_integer_spins(vertices, edges, colors):
    total_a = total_b = 0
    for assignment in itertools.product(range(colors), repeat=vertices):
        a, b = 1, 0
        for u, v, exponent in edges:
            if assignment[u] == assignment[v]:
                if exponent == 1:
                    a, b = -(colors - 2) * a - b, a
                else:
                    a, b = b, -a - (colors - 2) * b
        total_a += a
        total_b += b
    return [total_a, total_b]


class FactorizedExactPottsTests(unittest.TestCase):
    def test_integer_spin_sum_with_loops_isolated_and_disconnected_parts(self):
        rng = random.Random(509021)
        for case in range(80):
            vertices = rng.randrange(1, 6)
            colors = rng.randrange(5, 8)
            edges = [(rng.randrange(vertices), rng.randrange(vertices), rng.choice((-1, 1)))
                     for _ in range(rng.randrange(0, 9))]
            order = list(range(len(edges)))
            rng.shuffle(order)
            result = factorized_exact_partition(vertices, edges, order, colors=colors,
                                                 max_states=None, max_transitions=None)
            self.assertEqual(result["partition_function"],
                             brute_integer_spins(vertices, edges, colors), case)

    def test_q5_modular_reduction(self):
        rng = random.Random(542039)
        for _ in range(100):
            vertices = rng.randrange(1, 9)
            edges = [(rng.randrange(vertices), rng.randrange(vertices), rng.choice((-1, 1)))
                     for _ in range(rng.randrange(0, 13))]
            order = list(range(len(edges)))
            rng.shuffle(order)
            exact = factorized_exact_partition(vertices, edges, order, colors=5)
            modular = factorized_partition(vertices, edges, order)
            a, b = exact["partition_function"]
            self.assertEqual((a + b * POTTS_X) % PRIME, modular["partition_function"])

    def test_random_knots_and_shades_against_monolithic_exact(self):
        rng = random.Random(510786)
        for diagram in random_knots(80, seed=936732, max_crossings=14):
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            for colors in (5, 6, 7):
                shade = rng.choice((0, 1))
                expected = potts_exact(diagram, order=order, colors=colors, shade=shade,
                                       max_states=None, max_transitions=None)
                result = factorized_potts_exact(diagram, order=order, colors=colors,
                                                 shade=shade, max_states=None,
                                                 max_transitions=None)
                for field in ("partition_function", "unknot_partition", "differs", "shade",
                              "max_spin_frontier", "max_boundary"):
                    self.assertEqual(result[field], expected[field])

    def test_fixed_negative_control_q6(self):
        diagram = Diagram.from_braid(5, [-2, -3, 4, -4, 4, -4, -3, 2,
                                          -4, 1, 3, 4, 1, 1, 2, 3])
        order = [6, 12, 15, 0, 2, 10, 8, 4, 3, 5, 11, 13, 7, 14, 1, 9]
        global_result = potts_exact(diagram, order=order, max_states=None)
        result = factorized_potts_exact(diagram, order=order, max_states=None)
        self.assertEqual(result["partition_function"], global_result["partition_function"])
        self.assertLess(result["peak_component_states"], global_result["peak_states"])
        self.assertLess(result["transitions"], global_result["transitions"])

    def test_weaving_collision_q5_and_q6_resolution(self):
        for exponent in (5, 7, 11):
            diagram = Diagram.from_braid(3, [1, -2] * exponent)
            self.assertIsNone(factorized_potts_exact_obstruction(diagram, colors=5))
            self.assertIsNotNone(factorized_potts_exact_obstruction(diagram, colors=6))

    def test_budgets_empty_and_invalid_values(self):
        diagram = Diagram.from_braid(3, [1, -2, 1, -2])
        result = factorized_potts_exact(diagram)
        self.assertEqual(factorized_potts_exact(
            diagram, max_transitions=result["transitions"])["partition_function"],
            result["partition_function"])
        with self.assertRaises(FilterLimit):
            factorized_potts_exact(diagram, max_transitions=result["transitions"] - 1)
        for keyword in ("max_states", "max_transitions"):
            with self.assertRaises(FilterLimit):
                factorized_potts_exact(diagram, **{keyword: 0})
        self.assertIsNone(factorized_potts_exact_obstruction(Diagram.from_pd([]),
                                                           max_states=0, max_transitions=0))
        for invalid in (0, 4, True, 6.0):
            with self.assertRaises(ValueError):
                factorized_exact_partition(1, [(0, 0, 1)], [0], colors=invalid)
        with self.assertRaises(ValueError):
            factorized_exact_partition(2, [(0, 1, True)], [0])


if __name__ == "__main__":
    unittest.main()
