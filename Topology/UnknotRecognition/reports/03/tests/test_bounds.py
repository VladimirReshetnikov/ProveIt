import itertools
import unittest

from unknot_lab.hierarchy_bounds import HierarchyBound, cheeger_inequality_only


class BoundTests(unittest.TestCase):
    def test_potential_is_base_g_plus_one(self):
        bound = HierarchyBound(4, 3)
        self.assertEqual(bound.potential([4, 4, 4]), 124)
        self.assertEqual(bound.visit_bound(), 375)
        self.assertEqual(bound.conditional_work_bound(7, 2), 5250)

    def test_all_small_lexicographic_pairs(self):
        for g in range(1, 4):
            bound = HierarchyBound(g, 3)
            vectors = list(itertools.product(range(g + 1), repeat=3))
            for old in vectors:
                for new in vectors:
                    if new < old:
                        pivot = next(i for i in range(3) if old[i] != new[i])
                        self.assertTrue(bound.verify_reset(old, new, pivot))

    def test_arbitrary_tail_reset(self):
        bound = HierarchyBound(9, 4)
        self.assertTrue(bound.verify_reset([5, 3, 0, 0], [5, 2, 9, 9], 1))
        self.assertFalse(bound.verify_reset([5, 3, 0, 0], [5, 3, 0, 1], 1))
        self.assertFalse(bound.verify_reset([5, 3, 0, 0], [6, 2, 0, 0], 1))

    def test_zero_digits(self):
        bound = HierarchyBound(0, 4)
        self.assertEqual(bound.phase_bound(), 1)
        self.assertEqual(bound.potential([0]), 0)

    def test_guarded_hypotheses(self):
        with self.assertRaises(ValueError):
            HierarchyBound(2, 3).potential([3])
        with self.assertRaises(ValueError):
            HierarchyBound(2, 3).potential([0, 0, 0, 0])
        with self.assertRaises(ValueError):
            HierarchyBound(-1, 3)
        self.assertTrue(cheeger_inequality_only(1, 3, 6))
        self.assertFalse(cheeger_inequality_only(2, 3, 6))
        with self.assertRaises(ValueError):
            cheeger_inequality_only(0, 7, 6)


if __name__ == "__main__":
    unittest.main()
