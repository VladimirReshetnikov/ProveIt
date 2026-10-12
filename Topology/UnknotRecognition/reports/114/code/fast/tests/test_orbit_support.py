"""Support pruning preserves greedy proofs and binary contraction maps."""
import random
import unittest

from fastunknot.interval_merger import support_closure, restart_closure
from fastunknot.interval_orbits import IntervalPairing, periodic_merge, _contract
from test_interval_merge_queue import random_system


class OrbitSupportTests(unittest.TestCase):
    def test_random_greedy_closures_and_candidate_bound(self):
        rng = random.Random(261009465)
        for _ in range(400):
            _, pairs = random_system(rng)
            snapshot = list(pairs)
            for rule in ('fine_wilf', 'aht'):
                merger = lambda a, b: periodic_merge(a, b, periodic_rule=rule)
                expected_trace, trace = [], []
                expected = restart_closure(pairs, merge=merger, operations=expected_trace)
                result = support_closure(pairs, merge=merger, operations=trace)
                self.assertEqual(result.pairings, expected.pairings)
                self.assertEqual(trace, expected_trace)
                k = len(pairs)
                self.assertLessEqual(result.pair_tests, k*(k-1)//2+max(k-1, 0)**2)
                self.assertLessEqual(result.overlap_candidates, k*(k-1)//2)
            self.assertEqual(pairs, snapshot)

    def test_disjoint_supports_and_easy_merges_avoid_quadratic_candidates(self):
        for scale in (1, 1 << 20000):
            pairs = [IntervalPairing(4*i*scale, (4*i+1)*scale-1,
                                     (4*i+1)*scale, (4*i+2)*scale-1) for i in range(128)]
            result = support_closure(pairs, merge=periodic_merge)
            self.assertEqual(result.pairings, pairs)
            self.assertEqual(result.pair_tests, 1)
            self.assertEqual(result.overlap_candidates, 0)
            self.assertEqual(result.support_scans, 1)
            self.assertEqual(result.queue_runs, 0)
            result = support_closure([pairs[0]]*128, merge=periodic_merge)
            self.assertEqual(result.pairings, pairs[:1])
            self.assertEqual(result.pair_tests, 127)
            self.assertEqual(result.support_scans, 0)

    def test_dense_failed_scan_uses_bounded_queue_and_touching_supports_are_kept(self):
        pairs = [IntervalPairing(0, 3, 4, 7)]*32
        result = support_closure(pairs, merge=lambda a, b: None)
        self.assertEqual(result.pairings, pairs)
        self.assertEqual(result.queue_runs, 1)
        self.assertLessEqual(result.overlap_candidates, 32*31//2)
        # Pair 0 is disjoint; the later pair meets at exactly one point.
        pairs = [IntervalPairing(8, 8, 9, 9), IntervalPairing(0, 0, 1, 1),
                 IntervalPairing(1, 1, 2, 2)]
        trace = []
        result = support_closure(pairs, merge=periodic_merge, operations=trace)
        self.assertEqual(trace, [{'op': 'merge', 'left': 1, 'right': 2}])
        self.assertEqual(len(result.pairings), 2)

    def test_contraction_matches_literal_order_map_and_reuses_covered_rows(self):
        rng = random.Random(261009466)
        for _ in range(250):
            size, pairs = random_system(rng)
            occupied = sorted({x for p in pairs for lo, hi in ((p.a, p.b), (p.c, p.d))
                               for x in range(lo, hi+1)})
            size2, mapped, removed, gaps = _contract(size, pairs)
            self.assertEqual(size2, len(occupied))
            self.assertEqual(removed, size-len(occupied))
            self.assertEqual({x for lo, hi in gaps for x in range(lo, hi+1)},
                             set(range(size))-set(occupied))
            index = {x: i for i, x in enumerate(occupied)}
            self.assertEqual(mapped, [IntervalPairing(*(index[x] for x in (p.a,p.b,p.c,p.d)), p.reverse)
                                      for p in pairs])
            if not gaps:
                self.assertIs(mapped, pairs)
        scale = 1 << 20000
        pair = IntervalPairing(scale, 2*scale-1, 3*scale, 4*scale-1, True)
        size, rows, removed, gaps = _contract(5*scale, [pair])
        self.assertEqual((size, removed), (2*scale, 3*scale))
        self.assertEqual(rows, [IntervalPairing(0, scale-1, scale, 2*scale-1, True)])

    def test_cancellation_during_sweep_and_after_merge(self):
        for phase in ('scan', 'merge'):
            calls, trace = 0, []
            def check():
                nonlocal calls
                calls += 1
                if (phase == 'scan' and calls > 15) or (phase == 'merge' and trace):
                    raise RuntimeError('stop')
            pairs = ([IntervalPairing(3*i, 3*i, 3*i+1, 3*i+1) for i in range(32)]
                     if phase == 'scan' else [IntervalPairing(0, 3, 4, 7)]*32)
            with self.assertRaisesRegex(RuntimeError, 'stop'):
                support_closure(pairs, merge=periodic_merge, check=check, operations=trace)


if __name__ == '__main__':
    unittest.main()
