"""Deleted-suffix folds against direct finite pushforwards."""
import random
import unittest
from unittest.mock import patch

from fastunknot import weighted_orbits as producer
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


def partition(values):
    runs = []
    for i, value in enumerate(values):
        value = tuple(value)
        if runs and runs[-1][2] == value:
            runs[-1] = (runs[-1][0], i+1, value)
        else:
            runs.append((i, i+1, value))
    return runs


class FoldOverlayTests(unittest.TestCase):
    def test_direct_signed_pushforwards_and_two_jump_bound(self):
        rng = random.Random(261009443)
        for _ in range(2000):
            size = rng.randrange(2, 50)
            values = []
            value = (0, 0, 0)
            for i in range(size):
                if not i or rng.randrange(4) == 0:
                    value = tuple(rng.randrange(-5, 6) for _ in range(3))
                values.append(value)
            runs = partition(values)
            cut = rng.randrange(1, size)
            period = rng.randrange(1, cut+1)
            expected = [list(v) for v in values[:cut]]
            for x in range(cut, size):
                target = cut-period+(x-cut) % period
                for j, entry in enumerate(values[x]):
                    expected[target][j] += entry
            answer = producer._truncate_translation(runs, size, cut, period, 3, lambda: None)
            self.assertEqual(answer, partition(expected))
            self.assertLessEqual(len(answer), len(runs)+2)
            cut = rng.randrange((size+1)//2, size)
            left = rng.randrange(2*cut-size+1)
            expected = [list(v) for v in values[:cut]]
            for x in range(cut, size):
                for j, entry in enumerate(values[x]):
                    expected[left+size-1-x][j] += entry
            answer = producer._truncate_reflection(runs, size, cut, left, 3, lambda: None)
            self.assertEqual(answer, partition(expected))
            self.assertLessEqual(len(answer), len(runs)+2)

    def test_sharp_bound_on_actual_trace_and_independent_replay(self):
        pairs = [IntervalPairing(1,2,5,6), IntervalPairing(3,4,4,5), IntervalPairing(0,0,3,3)]
        observed = []
        original = producer._truncate_translation
        def trace(runs, size, cut, period, dimension, check):
            answer = original(runs, size, cut, period, dimension, check)
            observed.append((size, cut, period, runs, answer))
            return answer
        with patch.object(producer, '_truncate_translation', trace):
            answer = producer.weighted_orbit_histogram(7, pairs, [(0,7,(1,))], record_certificate=True)
        self.assertEqual(observed[0], (7,6,4,[(0,7,(1,))],
                                      [(0,2,(1,)),(2,3,(2,)),(3,6,(1,))]))
        with patch.object(producer, '_overlay_prefix', side_effect=AssertionError), \
             patch.object(producer, '_truncate_translation', side_effect=AssertionError):
            self.assertTrue(verify_weighted_orbit_certificate(7,pairs,[(0,7,(1,))],answer['certificate']))

    def test_untouched_prefix_sharing_zero_weights_and_late_cancellation(self):
        first, second = (11, -2, 0), (7, 3, -8)
        runs = [(0,3,first),(3,7,second),(7,10,(0,0,0))]
        answer = producer._truncate_translation(runs,10,9,2,3,lambda: None)
        self.assertIs(answer[0][2], first)
        self.assertIs(answer[1][2], second)
        self.assertEqual(answer, [(0,3,first),(3,7,second),(7,9,(0,0,0))])
        class Cancelled(Exception):
            pass
        calls = 0
        def count():
            nonlocal calls
            calls += 1
        producer._truncate_translation(runs,10,9,2,3,count)
        last = calls
        calls = 0
        def stop():
            nonlocal calls
            calls += 1
            if calls == last:
                raise Cancelled()
        with self.assertRaises(Cancelled):
            producer._truncate_translation(runs,10,9,2,3,stop)
        self.assertEqual(runs, [(0,3,first),(3,7,second),(7,10,(0,0,0))])
