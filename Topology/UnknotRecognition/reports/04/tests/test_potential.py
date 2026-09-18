from itertools import product
import unittest

from unknot.potential import HierarchyPotential


class PotentialTests(unittest.TestCase):
    def test_lexicographic_order(self):
        p = HierarchyPotential(3, 4)
        digits = list(product(range(4), repeat=4))
        self.assertEqual([p.value(v) for v in digits], list(range(256)))

    def test_padding(self):
        p = HierarchyPotential(5, 3)
        self.assertEqual(p.value([2]), p.value([2, 0, 0]))

    def test_worst_tail_reset(self):
        for g in range(1, 5):
            for depth in range(1, 5):
                p = HierarchyPotential(g, depth)
                for old in product(range(g + 1), repeat=depth):
                    for index, digit in enumerate(old):
                        if digit:
                            new = p.compress(old, index, digit-1, [g]*(depth-index-1))
                            self.assertLess(p.value(new), p.value(old))

    def test_inclusive_bound_needs_g_plus_one(self):
        p = HierarchyPotential(2, 2)
        self.assertEqual(p.value([1, 0]), 3)
        self.assertEqual(p.value([0, 2]), 2)
        self.assertEqual(p.phase_bound, 9)
        self.assertEqual(p.iteration_bound, 18)

    def test_invalid_updates(self):
        p = HierarchyPotential(2, 2)
        for values, index, digit, tail in [([1, 0], 0, 1, []), ([1], 1, 0, []),
                                          ([2], 0, -1, []), ([2], 0, 1, [2, 2])]:
            with self.subTest(values=values), self.assertRaises(ValueError):
                p.compress(values, index, digit, tail)

    def test_invalid_bounds_and_digits(self):
        for g, depth in [(-1, 1), (True, 1), (1, -1), (1, False)]:
            with self.assertRaises(ValueError):
                HierarchyPotential(g, depth)
        with self.assertRaises(ValueError):
            HierarchyPotential(2, 2).value([3])
        with self.assertRaises(ValueError):
            HierarchyPotential(2, 2).value([True])

    def test_zero_depth(self):
        p = HierarchyPotential(0, 0)
        self.assertEqual(p.value([]), 0)
        self.assertEqual(p.phase_bound, 1)
        self.assertEqual(p.iteration_bound, 0)


if __name__ == '__main__':
    unittest.main()
