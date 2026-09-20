"""Fast normalization and boundary checks; no third-party dependencies."""
import unittest
from fractions import Fraction
from verify import (
    bases_from_assignments, bases_from_ideals, boolean_coefficients,
    closure, contained_counts, direct_qzeta_negative, example_rows,
    general_downset_counterexample, interior_counts, is_preorder,
    support_counts, transpose, weighted_lattice_formula,
)


class ReciprocityTests(unittest.TestCase):
    def test_empty_ground_set(self):
        self.assertEqual(boolean_coefficients(()), [1])
        self.assertEqual(interior_counts(()), [1])
        self.assertEqual(direct_qzeta_negative((), 2), Fraction(1))

    def test_one_point_indexing(self):
        for q in (1, 2, 3, 5):
            self.assertEqual(direct_qzeta_negative((1,), q), Fraction(-1, q))

    def test_antichain(self):
        rows = (1, 2, 4)
        self.assertEqual(boolean_coefficients(rows), [0]*7 + [1])
        self.assertEqual(bases_from_ideals(rows), ((1, 1, 1),))

    def test_two_element_chain(self):
        self.assertEqual(boolean_coefficients((3, 2)), [0, 0, 1, 1])

    def test_equivalent_elements_remain_distinct(self):
        rows = (7, 7, 7)
        self.assertEqual(boolean_coefficients(rows), [0, 1, 1, 2, 1, 2, 2, 1])
        self.assertEqual(len(bases_from_assignments(rows)), 10)

    def test_support_interior_identity(self):
        rows = example_rows()["source_example_5"]
        c = support_counts(bases_from_ideals(rows), 5)
        self.assertEqual(c, boolean_coefficients(rows))
        self.assertEqual(contained_counts(c), interior_counts(rows))
        self.assertEqual(c[24], 2)  # exact support {d,e}
        self.assertEqual(c[31], 1)

    def test_zero_capacity_shift(self):
        for rows in example_rows().values():
            self.assertEqual(weighted_lattice_formula(rows, (0,)*len(rows)), 1)

    def test_cover_count_is_not_rank(self):
        rows = example_rows()["fork_3"]
        self.assertEqual(direct_qzeta_negative(rows, 2), Fraction(-5, 8))
        self.assertNotEqual(direct_qzeta_negative(rows, 2), Fraction(-3, 8))

    def test_nontransitivity_is_not_silently_accepted(self):
        rows = (3, 6, 5)
        self.assertFalse(is_preorder(rows))
        self.assertEqual(closure(rows), (7, 7, 7))
        bad = general_downset_counterexample()
        self.assertNotEqual(bad["signed_boolean_support_coefficients"],
                            bad["actual_support_coefficients"])

    def test_dual_orientation(self):
        rows = (7, 2, 4)
        self.assertEqual(transpose(rows), (1, 3, 5))
        self.assertNotEqual(boolean_coefficients(rows),
                            boolean_coefficients(transpose(rows)))


if __name__ == "__main__":
    unittest.main()
