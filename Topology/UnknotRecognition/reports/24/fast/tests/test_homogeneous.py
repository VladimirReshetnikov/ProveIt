"""The cardinality filter, generic fallback, and actual scanner grading."""
import itertools
import random
import unittest
from unittest.mock import patch

from fastunknot.frobenius.subset import (homogeneous_degree, pack, subset_product_fast,
    subset_product_ranked, subset_product_sparse, subset_product)
from fastunknot.frobenius.kernel import CompiledPlan, contract_reference
from fastunknot import Diagram, khovanov_rank
from audit_grading import GradingAuditScan


class HomogeneousTests(unittest.TestCase):
    def test_all_four_variable_homogeneous_polynomials(self):
        # Every subset of each degree layer, including different input degrees.
        layers = [[s for s in range(16) if s.bit_count() == degree] for degree in range(5)]
        polynomials = {0}
        for layer in layers:
            polynomials.update(pack((s for j, s in enumerate(layer) if (choice >> j) & 1), 4)
                               for choice in range(1 << len(layer)))
        for f, g in itertools.product(sorted(polynomials), repeat=2):
            expected = subset_product_sparse(f, g, 4, polarize=False)
            self.assertEqual(subset_product_fast(f, g, 4), expected)
            self.assertEqual(subset_product_ranked(f, g, 4), expected)

    def test_overlap_cannot_survive_union_transform(self):
        # x0 * (x0+x1) must discard the union x0 and retain x0*x1.
        self.assertEqual(subset_product_fast(1 << 1, (1 << 1) | (1 << 2), 3), 1 << 3)
        f = pack([3, 5], 3)
        g = pack([3, 6], 3)
        self.assertEqual(subset_product_fast(f, g, 3), 0)

    def test_complementary_top_degree_with_byte_padding(self):
        for variables in range(2, 8):
            for a in range(1, variables):
                f = pack((s for s in range(1 << variables) if s.bit_count() == a), variables)
                g = pack((s for s in range(1 << variables)
                          if s.bit_count() == variables - a and s % 3), variables)
                self.assertEqual(subset_product_fast(f, g, variables),
                                 subset_product_sparse(f, g, variables, polarize=False))

    def test_checked_fallback_for_general_inputs(self):
        f, g = pack([0, 1, 3], 3), pack([2, 7], 3)
        with patch('fastunknot.frobenius.subset.subset_product_ranked', wraps=subset_product_ranked) as old:
            self.assertEqual(subset_product_fast(f, g, 3), subset_product_sparse(f, g, 3))
            old.assert_called_once()
        with patch('fastunknot.frobenius.subset.subset_product_ranked', side_effect=AssertionError('ranked path')):
            self.assertEqual(subset_product_fast(2, 6, 3), 8)

    def test_degree_and_limits(self):
        self.assertEqual(homogeneous_degree(0), -1)
        self.assertEqual(homogeneous_degree(1), 0)
        self.assertEqual(homogeneous_degree(pack([3, 5, 6], 3)), 2)
        self.assertIsNone(homogeneous_degree(3))
        for value in (-1, True):
            with self.assertRaises(ValueError):
                homogeneous_degree(value)
        with self.assertRaises(MemoryError):
            subset_product(2, 6, 3, method='fast', dense_limit=2)
        def stop():
            raise TimeoutError('deadline')
        with self.assertRaises(TimeoutError):
            subset_product_fast(2, 6, 3, check=stop)

    def test_seeded_homogeneous_products_and_projections(self):
        rng = random.Random(2026100802)
        for variables in range(2, 11):
            for _ in range(20):
                degrees = [rng.randrange(variables+1) for _ in range(2)]
                f, g = [pack((s for s in range(1 << variables)
                              if s.bit_count() == degree and rng.randrange(2)), variables)
                        for degree in degrees]
                self.assertEqual(subset_product_fast(f, g, variables),
                                 subset_product_sparse(f, g, variables))
        cp = CompiledPlan.from_plan(((3, 1, 3, 0), (4, 6, 4, 0)))
        for f in (pack([1, 2, 4], 3), pack([3, 5, 6], 3)):
            projected = cp.project(f, 0)
            if projected:
                self.assertEqual(homogeneous_degree(projected), homogeneous_degree(f))
            for g in (pack([1, 2, 4], 3), pack([3, 5, 6], 3)):
                self.assertEqual(cp.apply(f, g, method='fast'), contract_reference(cp.components, f, g))

    def test_recovered_quantum_shifts_and_adaptive_compatibility(self):
        for strands, word in ((2, [1]*7), (3, [1, -2]*4),
                              (4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2])):
            diagram = Diagram.from_braid(strands, word)
            scan = GradingAuditScan(shape_cache=False)
            for crossing in diagram.pd:
                scan.add_crossing(crossing)
                scan.check_d_squared()
            changed = khovanov_rank(diagram.pd, order=list(range(len(word))),
                                    composition='component-dense', reduction='adaptive', check_d_squared=True)
            self.assertEqual(changed['by_degree'], scan.ranks_by_degree())
            self.assertGreater(scan.checked_entries, 0)


if __name__ == '__main__':
    unittest.main()

