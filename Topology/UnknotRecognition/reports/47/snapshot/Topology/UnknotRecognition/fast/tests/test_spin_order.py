"""Regression for a supplied order that masks a smaller greedy frontier."""
import random
import unittest

from fastunknot.diagram import Diagram
from fastunknot.separator_order import verify_width_bounded_order
from fastunknot.spin_jones import spin_jones_exact
from disk_grid import descending_grid


class SpinOrderTests(unittest.TestCase):
    def test_shuffled_grid_keeps_the_greedy_candidate_before_certification(self):
        diagram = Diagram.from_pd(descending_grid(8))
        order = list(range(diagram.crossings))
        random.Random(26100859).shuffle(order)
        # The initial policy exhausted 4096 states on this exact supplied order.
        result = spin_jones_exact(diagram, order=order, include_polynomial=True)
        self.assertEqual(result['jones_polynomial']['coefficients_hex'], [[0, '0x1']])
        self.assertEqual(result['max_boundary'], 10)
        self.assertLess(result['peak_states'], 4096)
        self.assertTrue(verify_width_bounded_order(diagram.pd, result['order_certificate']))


if __name__ == '__main__':
    unittest.main()
