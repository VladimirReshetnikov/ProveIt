import unittest
from friendly import FinitePoset, naturally_labeled_posets


class FriendlyTests(unittest.TestCase):
    def test_empty(self):
        p = FinitePoset(())
        self.assertEqual(p.exact_rank(), 0)
        self.assertEqual(p.graph_rank(), 0)
        self.assertEqual(p.optimal_witness(), ())

    def test_chains(self):
        for n in range(10):
            p = FinitePoset.chain(n)
            self.assertEqual(p.exact_rank(), 0)
            self.assertEqual(len(p.components()), n)

    def test_antichains(self):
        for n in range(9):
            p = FinitePoset.antichain(n)
            self.assertEqual(p.exact_rank(), max(n - 1, 0))
            self.assertEqual(len(p.optimal_witness()), max(n - 1, 0))

    def test_non_natural_labels(self):
        # Ordinal sum of {2,4}, {0}, {1,3}, in this deliberately scrambled labeling.
        p = FinitePoset.from_relations(5, [(2, 0), (4, 0), (0, 1), (0, 3)])
        self.assertEqual(p.ordered_components(), ((1 << 2) | (1 << 4), 1,
                                                 (1 << 1) | (1 << 3)))
        self.assertEqual(p.exact_rank(), 2)
        self.assertEqual(len(p.optimal_witness()), 2)

    def test_small_exhaustive(self):
        expected = [1, 1, 2, 7, 40, 357]
        for n, count in enumerate(expected):
            generated = list(naturally_labeled_posets(n))
            self.assertEqual(len(generated), count)
            self.assertEqual(len({p.up for p in generated}), count)
            for p in generated:
                self.assertEqual(p.exact_rank(), p.graph_rank())
                self.assertEqual(len(p.optimal_witness()), p.graph_rank())

    def test_ordinal_sum(self):
        samples = [p for n in range(4) for p in naturally_labeled_posets(n)]
        for p in samples:
            for q in samples:
                self.assertEqual(p.ordinal_sum(q).exact_rank(),
                                 p.exact_rank() + q.exact_rank())

    def test_disjoint_sum(self):
        samples = [p for n in range(1, 4) for p in naturally_labeled_posets(n)]
        for p in samples:
            for q in samples:
                self.assertEqual(p.disjoint_sum(q).exact_rank(), p.n + q.n - 1)

    def test_grid(self):
        for m in range(2, 6):
            for n in range(2, 6):
                p = FinitePoset.chain(m).product(FinitePoset.chain(n))
                self.assertEqual(p.exact_rank(), m * n - 3)

    def test_invalid_relations(self):
        for up in [(0,), (3, 3), (3, 6, 4), (9, 2)]:
            with self.assertRaises(ValueError):
                FinitePoset(up)
        with self.assertRaises(ValueError):
            FinitePoset.from_relations(2, [(0, 1), (1, 0)])
        with self.assertRaises(ValueError):
            FinitePoset.chain(2).exact_rank(4)

    def test_invalid_sequences(self):
        p = FinitePoset.antichain(3)
        self.assertTrue(p.is_friendly([0, 1]))
        self.assertFalse(p.is_friendly([0, 0]))
        self.assertFalse(p.is_friendly([0, 1, 2]))
        self.assertFalse(p.is_friendly([3]))


if __name__ == "__main__":
    unittest.main()
