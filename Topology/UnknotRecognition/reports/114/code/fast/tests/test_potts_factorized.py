"""Exact orbit-alignment and processed-component tensor tests."""
import itertools
import math
import random
import unittest

from fastunknot.diagram import Diagram
from fastunknot.filters import FilterLimit, PRIME, jones_obstruction
from fastunknot.potts import potts_bracket, potts_obstruction
from fastunknot.potts_factorized import (factorized_partition,
                                        factorized_potts_bracket,
                                        factorized_potts_obstruction,
                                        relative_alignments)
from test_potts import random_knots


def brute_spins(vertices, edges, colors, weights):
    answer = 0
    for assignment in itertools.product(range(colors), repeat=vertices):
        term = 1
        for u, v, exponent in edges:
            if assignment[u] == assignment[v]:
                term = term * weights[exponent] % PRIME
        answer += term
    return answer % PRIME


class FactorizedPottsTests(unittest.TestCase):
    def test_all_relative_orbit_cardinalities(self):
        for colors in range(1, 7):
            falling = [math.factorial(colors) // math.factorial(colors - k)
                       for k in range(colors + 1)]
            for left in range(colors + 1):
                for right in range(colors + 1):
                    alignments = list(relative_alignments(left, right, colors))
                    self.assertEqual(len(set(alignments)), len(alignments))
                    self.assertEqual(sum(falling[used] for _, used in alignments),
                                     falling[left] * falling[right])
                    self.assertLessEqual(len(alignments), math.factorial(colors))
                    for alignment, used in alignments:
                        self.assertEqual(len(set(alignment)), right)
                        self.assertLessEqual(used, colors)
                    if left and right:
                        self.assertEqual(sum(falling[used] for mapping, used in alignments
                                             if mapping[0] == 0) * colors,
                                         falling[left] * falling[right])

    def test_random_graphs_against_all_labeled_spins(self):
        rng = random.Random(49317)
        for case in range(100):
            vertices = rng.randrange(1, 7)
            colors = rng.randrange(1, 7)
            edges = [(rng.randrange(vertices), rng.randrange(vertices), rng.choice((-1, 1)))
                     for _ in range(rng.randrange(0, 10))]
            order = list(range(len(edges)))
            rng.shuffle(order)
            weights = {-1: rng.randrange(1, 20), 1: rng.randrange(1, 20)}
            result = factorized_partition(vertices, edges, order, colors=colors,
                                           equal_weights=weights, max_states=None,
                                           max_transitions=None)
            self.assertEqual(result["partition_function"],
                             brute_spins(vertices, edges, colors, weights), case)

    def test_disconnected_products_loops_and_isolated_vertices(self):
        edges = [(0, 1, 1), (2, 3, -1), (0, 0, -1), (2, 3, 1)]
        weights = {1: 7, -1: 13}
        for order in itertools.permutations(range(4)):
            result = factorized_partition(5, edges, order, colors=5,
                                           equal_weights=weights)
            self.assertEqual(result["partition_function"],
                             brute_spins(5, edges, 5, weights))

    def test_knot_random_orders_against_global_spin_tensor(self):
        rng = random.Random(72497)
        for diagram in random_knots(160, seed=46424, max_crossings=16):
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            for shade in (None, 0, 1):
                global_result = potts_bracket(diagram, order=order, shade=shade,
                                              max_states=None, max_transitions=None)
                factored = factorized_potts_bracket(diagram, order=order, shade=shade,
                                                    max_states=None, max_transitions=None)
                for field in ("partition_function", "bracket", "unknot_bracket",
                              "max_spin_frontier", "max_boundary", "shade"):
                    self.assertEqual(global_result[field], factored[field])

    def test_fixed_negative_control_is_compressed(self):
        word = [-2, -3, 4, -4, 4, -4, -3, 2, -4, 1, 3, 4, 1, 1, 2, 3]
        order = [6, 12, 15, 0, 2, 10, 8, 4, 3, 5, 11, 13, 7, 14, 1, 9]
        diagram = Diagram.from_braid(5, word)
        global_result = potts_bracket(diagram, order=order)
        factored = factorized_potts_bracket(diagram, order=order)
        self.assertEqual(global_result["bracket"], factored["bracket"])
        self.assertEqual(global_result["peak_states"], 3845)
        self.assertEqual(factored["peak_component_states"], 202)
        self.assertLess(factored["transitions"], global_result["transitions"])

    def test_q5_blind_weaving_family_is_inconclusive(self):
        for exponent in (5, 7, 11):
            diagram = Diagram.from_braid(3, [1, -2] * exponent)
            self.assertIsNone(potts_obstruction(diagram))
            self.assertIsNone(factorized_potts_obstruction(diagram))
            self.assertIsNotNone(jones_obstruction(diagram))

    def test_resource_and_empty_contracts(self):
        diagram = Diagram.from_braid(3, [1, -2, 1, -2])
        result = factorized_potts_bracket(diagram)
        self.assertEqual(factorized_potts_bracket(
            diagram, max_transitions=result["transitions"])["bracket"], result["bracket"])
        with self.assertRaises(FilterLimit):
            factorized_potts_bracket(diagram, max_transitions=result["transitions"] - 1)
        for keyword in ("max_states", "max_transitions"):
            with self.assertRaises(FilterLimit):
                factorized_potts_bracket(diagram, **{keyword: 0})
        self.assertIsNone(factorized_potts_obstruction(Diagram.from_pd([]),
                                                      max_states=0, max_transitions=0))
        with self.assertRaises(ValueError):
            factorized_partition(2, [(0, 2, 1)], [0])
        with self.assertRaises(ValueError):
            factorized_partition(2, [(0, 1, 1)], [0], colors=4)
        for invalid in (1.5, True, "7"):
            with self.assertRaises(ValueError):
                factorized_partition(2, [(0, 1, 1)], [0], equal_weights={1: invalid})


if __name__ == "__main__":
    unittest.main()
