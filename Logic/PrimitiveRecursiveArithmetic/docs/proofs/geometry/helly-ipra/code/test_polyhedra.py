from fractions import Fraction as Q
import unittest

from polyhedra import Feasible, Infeasible, decide_family, satisfies, solve


class PolyhedraTests(unittest.TestCase):

    def test_zero_dimensions_and_no_constraints(self):
        self.assertEqual(solve(0, [((), 0)]), ())
        self.assertIsNone(solve(0, [((), -1)]))
        self.assertEqual(solve(3, []), (0, 0, 0))
        self.assertEqual(decide_family(2, []), Feasible((0, 0)))

    def test_half_lines(self):
        self.assertEqual(solve(1, [((-2,), -1)]), (Q(1, 2),))
        self.assertEqual(solve(1, [((3,), -2)]), (Q(-2, 3),))

    def test_equality(self):
        rows = [((2, 1), 1), ((-2, -1), -1), ((1, -1), 0), ((-1, 1), 0)]
        self.assertEqual(solve(2, rows), (Q(1, 3), Q(1, 3)))

    def test_group_obstruction(self):
        groups = [[((-1, 0), 0)], [((0, -1), 0)], [((1, 1), -1)], []]
        obstruction = decide_family(2, groups)
        self.assertIsInstance(obstruction, Infeasible)
        self.assertEqual(obstruction.indices, (0, 1, 2))
        for omit in range(3):
            rows = [r for i in range(3) if i != omit for r in groups[i]]
            self.assertTrue(satisfies(solve(2, rows), rows))

    def test_constructive_alternative(self):
        groups = [[((1, 0), 3)], [((-1, 0), -1)], [((0, -2), -1)], [((1, 1), 2)]]
        answer = decide_family(2, groups)
        self.assertIsInstance(answer, Feasible)
        for rows in groups:
            self.assertTrue(satisfies(answer.point, rows))
