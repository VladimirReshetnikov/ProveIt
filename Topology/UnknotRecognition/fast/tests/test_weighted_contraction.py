"""Static contraction against literal deletion and independent orbit replay."""
from collections import Counter
import random
import unittest
from unittest.mock import patch

from fastunknot import weighted_orbits as producer
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


def partition(values):
    runs = []
    for i, value in enumerate(values):
        if runs and runs[-1][2] == value:
            runs[-1] = (runs[-1][0], i + 1, value)
        else:
            runs.append((i, i + 1, value))
    return runs


class WeightedContractionTests(unittest.TestCase):
    def test_literal_signed_deletion_and_emission_counters(self):
        rng = random.Random(26101101)
        for _ in range(2000):
            size = rng.randrange(80)
            values = []
            for i in range(size):
                values.append(tuple(rng.randrange(-3, 4) for _ in range(3))
                              if not i or rng.randrange(4) == 0 else values[-1])
            deleted = [rng.randrange(2) == 0 for _ in range(size)]
            gaps = [(a, b - 1) for a, b, value in partition(deleted) if value]
            runs = partition(values)
            histogram = Counter({(91, -4, 0): 7})
            expected = histogram + Counter()  # retain initial histogram
            for i in range(size):
                if deleted[i]:
                    expected[values[i]] += 1
            survivors, emitted = producer._contract_weights(
                runs, size, gaps, histogram, lambda: None)
            self.assertEqual(survivors, partition([v for i, v in enumerate(values) if not deleted[i]]))
            self.assertEqual(histogram, expected)
            self.assertEqual(emitted, sum(max(a, c) < min(b, d + 1)
                                         for a, b, _ in runs for c, d in gaps))
            self.assertEqual(runs, partition(values))

    def test_binary_endpoints_coalescing_and_vector_sharing(self):
        end = 1 << 16384
        value, middle = (7, -3), (9, 2)
        runs = [(0, 3, value), (3, end - 2, middle), (end - 2, end, value)]
        histogram = {}
        result, emitted = producer._contract_weights(
            runs, end, [(3, end - 3)], histogram, lambda: None)
        self.assertEqual(result, [(0, 5, value)])
        self.assertIs(result[0][2], value)
        self.assertEqual(histogram, {middle: end - 5})
        self.assertEqual(emitted, 1)

    def test_linear_sweep_independent_replay_and_cancellation(self):
        runs = [(i, i + 1, (i,)) for i in range(1000)]
        gaps = [(i, i) for i in range(0, 1000, 2)]
        calls = 0
        def poll():
            nonlocal calls
            calls += 1
        producer._contract_weights(runs, 1000, gaps, {}, poll)
        self.assertLessEqual(calls, len(runs) + 2 * len(gaps))
        class Stop(Exception):
            pass
        def cancel():
            raise Stop()
        with self.assertRaises(Stop):
            producer._contract_weights(runs, 1000, gaps, {}, cancel)
        pairs = [IntervalPairing(3, 6, 20, 23)]
        weights = [(0, 28, (1, -2)), (6, 9, (-3, 5))]
        result = producer.weighted_orbit_histogram(28, pairs, weights, record_certificate=True)
        with patch.object(producer, '_contract_weights', side_effect=AssertionError('producer')):
            self.assertTrue(verify_weighted_orbit_certificate(28, pairs, weights, result['certificate']))


if __name__ == '__main__':
    unittest.main()
