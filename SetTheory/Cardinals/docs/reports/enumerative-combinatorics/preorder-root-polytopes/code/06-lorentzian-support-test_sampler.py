#!/usr/bin/env python3
"""Small deterministic interface/feasibility tests, not mixing proofs."""
from fractions import Fraction
from math import comb
import unittest

from support_sampler import ceil_log2, sample_supports
from verify import pair_data, ulc


class SamplerTests(unittest.TestCase):
    def test_empty_donors(self):
        result = sample_supports((), 3, 5, seed=1)
        self.assertEqual(result['support_masks'], [0] * 5)
        self.assertEqual(result['burn_in_steps_per_sample'], 0)

    def test_no_receivers(self):
        result = sample_supports((0, 0), 0, 5, seed=2)
        self.assertEqual(result['support_masks'], [0] * 5)

    def test_weighted_supports_are_feasible(self):
        rows = (14, 3, 5, 9)
        result = sample_supports(rows, 4, 50, weights=(Fraction(1, 3),
            Fraction(2), Fraction(7, 2), Fraction(1)), seed=20260929)
        counts, _ = pair_data(rows, 4)
        self.assertTrue(all(counts[s] > 0 for s in result['support_masks']))

    def test_seed_reproducibility(self):
        first = sample_supports((3, 3), 2, 10, seed=7)
        second = sample_supports((3, 3), 2, 10, seed=7)
        self.assertEqual(first['support_masks'], second['support_masks'])

    def test_reject_bad_inputs(self):
        bad_calls = [((4,), 2, 2), ((-1,), 2, 2), ((1,), 1, -1)]
        for rows, n, count in bad_calls:
            with self.assertRaises(ValueError):
                sample_supports(rows, n, count)
        with self.assertRaises(ValueError):
            sample_supports((1,), 1, 2, weights=(Fraction(0),))
        with self.assertRaises(ValueError):
            sample_supports((1,), 1, 2, epsilon=Fraction(0))

    def test_logarithm_budget(self):
        for x in [Fraction(1, 5), Fraction(1), Fraction(3, 2),
                  Fraction(4), Fraction(257, 4), Fraction(1000000)]:
            k = ceil_log2(x)
            self.assertGreaterEqual(Fraction(1 << k), x)
            if k:
                self.assertLess(Fraction(1 << (k-1)), x)

    def test_tilting_mass_bound(self):
        # Exact finite audit of Lemma 7.3 on every unweighted (3,3) graph.
        # Activities need not be the tuning algorithm's own grid: the lemma
        # concerns any tilt for which both tails carry at least one quarter.
        for encoding in range(512):
            rows = tuple((encoding >> (3*x)) & 7 for x in range(3))
            counts, _ = pair_data(rows, 3)
            a = [sum(count for mask, count in enumerate(counts)
                     if mask.bit_count() == k) for k in range(4)]
            ulc(a, 3)
            d = max(k for k, v in enumerate(a) if v)
            for t in [Fraction(1, 4), Fraction(1, 2), Fraction(1),
                      Fraction(2), Fraction(4)]:
                masses = [a[k]*t**k for k in range(d+1)]
                total = sum(masses)
                for k in range(1, d+1):
                    lower = sum(masses[:k])
                    if 4*lower >= total and 4*(total-lower) >= total:
                        self.assertGreaterEqual(4*(d+1)*masses[k], total)


if __name__ == '__main__':
    unittest.main(verbosity=2)
