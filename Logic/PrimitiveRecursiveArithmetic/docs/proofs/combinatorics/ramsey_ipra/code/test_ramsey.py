"""Run with python3 test_ramsey.py -v. No third-party packages are needed."""

import unittest

from ramsey import Coloring, Witness, bound_up_to, find_witness, image_mask, stabilize, submasks, verify


def graph_from_assignment(n: int, assignment: int) -> Coloring:
    digits = [0] * (1 << n)
    for i, edge in enumerate(submasks((1 << n) - 1, 2)):
        digits[edge] = (assignment >> i) & 1
    return Coloring(n, 2, 2, tuple(digits))


class RamseyTests(unittest.TestCase):
    def test_edge_cases(self):
        for k in (0, 1, 2, 3):
            table = Coloring.tabulate(3, 0, 3, lambda _: 2)
            self.assertEqual(find_witness(table, k), Witness((1 << k) - 1, 2))
            self.assertTrue(verify(table, k, find_witness(table, k)))
        empty = Coloring.tabulate(0, 1, 1, lambda _: 0)
        self.assertEqual(find_witness(empty, 0), Witness(0, 0))
        self.assertIsNone(find_witness(empty, 1))
        vacuous = Coloring.tabulate(4, 5, 2, lambda _: 1)
        self.assertEqual(find_witness(vacuous, 2), Witness(3, 0))
        self.assertTrue(verify(vacuous, 2, Witness(3, 1)))
        self.assertFalse(verify(vacuous, 2, Witness(3, 2)))
        self.assertFalse(verify(vacuous, 2, Witness(17, 0)))

    def test_encoding(self):
        for colors in (1, 2, 3):
            table = Coloring.tabulate(4, 2, colors, lambda edge: edge % colors)
            self.assertEqual(table, Coloring.decode(4, 2, colors, table.encode()))
        with self.assertRaises(ValueError):
            Coloring.decode(2, 1, 2, 1 << 4)
        with self.assertRaises(ValueError):
            Coloring.decode(0, 0, 1, 1)

    def test_sharpened_bounds(self):
        self.assertIsNone(bound_up_to(2, 3, 2, 15))
        self.assertEqual(bound_up_to(2, 3, 2, 16), 16)
        self.assertEqual(bound_up_to(2, 4, 2, 100), 96)
        bound = 17 * 2**105
        self.assertIsNone(bound_up_to(3, 4, 2, bound - 1))
        self.assertEqual(bound_up_to(3, 4, 2, bound), bound)
        self.assertIsNone(bound_up_to(800, 801, 2, 10**100))
        self.assertEqual(bound_up_to(800, 801, 1, 802), 801)
        self.assertEqual(bound_up_to(9, 2, 5, 7), 2)

    def test_all_graphs_on_five_and_six_vertices(self):
        # The labeled 5-cycles are exactly the 12 exceptional colorings on K5.
        for n, expected_failures in ((5, 12), (6, 0)):
            edge_count = n * (n - 1) // 2
            failures = 0
            for assignment in range(1 << edge_count):
                table = graph_from_assignment(n, assignment)
                witness = find_witness(table, 3)
                if witness is None:
                    failures += 1
                else:
                    self.assertTrue(verify(table, 3, witness))
            self.assertEqual(failures, expected_failures)

    def check_reduction(self, table, length, k):
        result = stabilize(table, length)
        self.assertIsNotNone(result)
        self.assertLess(result.vertices[-1], result.sentinel)
        # Every upper edge, including those through z, has the claimed color.
        vertices = result.vertices + (result.sentinel,)
        for edge in submasks((1 << len(vertices)) - 1, table.arity):
            initial = edge ^ (1 << (edge.bit_length() - 1))
            self.assertEqual(table.digits[image_mask(edge, vertices)],
                             result.reduced.digits[initial])
        witness = find_witness(result.reduced, k)
        self.assertIsNotNone(witness)
        self.assertTrue(verify(table, k + 1, result.lift(witness)))

    def test_graph_reduction(self):
        parity = lambda edge: sum(i for i in range(10) if edge & (1 << i)) % 2
        self.check_reduction(Coloring.tabulate(10, 2, 2, parity), 4, 3)

    def test_triple_reduction(self):
        parity = lambda edge: sum(i for i in range(12) if edge & (1 << i)) % 2
        self.check_reduction(Coloring.tabulate(12, 3, 2, parity), 5, 3)

    def test_small_reservoir(self):
        table = Coloring.tabulate(2, 2, 2, lambda _: 0)
        self.assertIsNone(stabilize(table, 2))
        result = stabilize(table, 0)
        self.assertEqual(result.vertices, ())
        self.assertEqual(result.sentinel, 0)
        self.assertTrue(verify(table, 1, result.lift(Witness(0, 0))))


if __name__ == "__main__":
    unittest.main()
