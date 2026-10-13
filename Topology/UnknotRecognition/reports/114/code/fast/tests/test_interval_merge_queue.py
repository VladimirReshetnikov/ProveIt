"""Exact legacy traces, independent orbit answers, and merger work bounds."""

import random
import unittest

from fastunknot.interval_merger import (
    hybrid_closure, periodic_closure, restart_closure,
)
from fastunknot.interval_orbits import IntervalPairing, count_orbits, periodic_merge
from fastunknot.interval_orbit_verify import verify_orbit_certificate


def five_cycle_system(m, period_scale=None):
    period_scale = 10 * m if period_scale is None else period_scale
    pairs = [IntervalPairing(i, period_scale + 2*i - 1,
                             period_scale + 2*i, 2*period_scale + 3*i - 1)
             for i in range(m + 1)]
    return 2*period_scale + 3*m, pairs[:-1] + [pairs[-1]] * m


def literal_count(size, pairs):
    adjacency = [[] for _ in range(size)]
    for pair in pairs:
        for point in range(pair.a, pair.b + 1):
            target = pair.a + pair.d - point if pair.reverse else point + pair.c - pair.a
            adjacency[point].append(target)
            adjacency[target].append(point)
    seen = set()
    count = 0
    for point in range(size):
        if point in seen:
            continue
        count += 1
        pending = [point]
        seen.add(point)
        while pending:
            for target in adjacency[pending.pop()]:
                if target not in seen:
                    seen.add(target)
                    pending.append(target)
    return count


def random_system(rng):
    size = rng.randrange(1, 45)
    pairs = []
    for _ in range(rng.randrange(0, 24)):
        width = rng.randrange(1, size + 1)
        a, c = (rng.randrange(size - width + 1) for _ in range(2))
        pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                      bool(rng.getrandbits(1))))
    return size, pairs


class IntervalMergeQueueTests(unittest.TestCase):
    def test_random_closures_preserve_the_greedy_trace_and_bound(self):
        rng = random.Random(20261009422)
        for trial in range(600):
            _, pairs = random_system(rng)
            for rule in ('fine_wilf', 'aht'):
                merger = lambda a, b: periodic_merge(a, b, periodic_rule=rule)
                expected_trace = []
                expected = restart_closure(pairs, merge=merger,
                                             operations=expected_trace)
                k = len(pairs)
                for method in (periodic_closure, hybrid_closure):
                    trace = []
                    actual = method(pairs, merge=merger, operations=trace)
                    self.assertEqual(actual.pairings, expected.pairings)
                    self.assertEqual(trace, expected_trace)
                    self.assertEqual(actual.mergers, expected.mergers)
                    allowance = max(k - 1, 0)**2
                    if method is hybrid_closure:
                        allowance += k * (k - 1) // 2
                    self.assertLessEqual(actual.pair_tests, allowance)

    def test_complete_counts_match_literal_graphs_and_independent_replay(self):
        rng = random.Random(20261009423)
        for _ in range(120):
            size, pairs = random_system(rng)
            expected = literal_count(size, pairs)
            for rule in ('fine_wilf', 'aht'):
                reference = None
                for scheduler in ('legacy', 'adaptive', 'queue'):
                    result = count_orbits(size, pairs, periodic_rule=rule,
                                          merger_scheduler=scheduler,
                                          record_certificate=True)
                    self.assertEqual(result.orbits, expected)
                    self.assertTrue(verify_orbit_certificate(size, pairs,
                                                              result.certificate))
                    if reference is not None:
                        self.assertEqual(result.certificate, reference.certificate)
                        self.assertEqual(result.cycles, reference.cycles)
                    reference = result

    def test_five_cycle_family_has_exact_cubic_and_quadratic_work(self):
        for m in (2, 3, 4, 8, 16):
            size, pairs = five_cycle_system(m)
            reference = count_orbits(size, pairs, merger_scheduler='legacy',
                                      record_certificate=True)
            queued = count_orbits(size, pairs, merger_scheduler='queue',
                                   record_certificate=True)
            adaptive = count_orbits(size, pairs, record_certificate=True)
            self.assertEqual(reference.cycles, 5)
            self.assertEqual(reference.orbits, 1)
            self.assertEqual(literal_count(size, pairs), 1)
            self.assertEqual(reference.stats['pair_tests'],
                             m**3 + (m*m + 5*m)//2 - 4)
            self.assertEqual(queued.stats['pair_tests'], 5*m*m - 6*m + 2)
            for result in (queued, adaptive):
                self.assertEqual(result.certificate, reference.certificate)
                self.assertEqual(result.cycles, 5)
                self.assertTrue(verify_orbit_certificate(size, pairs,
                                                          result.certificate))
            if m >= 3:
                self.assertEqual(adaptive.stats['merger_queue_switches'], 1)

    def test_large_binary_endpoints_keep_the_five_cycle_trace_pattern(self):
        size, pairs = five_cycle_system(8, (1 << 4096) + 80)
        expected = None
        for scheduler in ('legacy', 'adaptive', 'queue'):
            result = count_orbits(size, pairs, merger_scheduler=scheduler,
                                  record_certificate=True)
            self.assertEqual(result.cycles, 5)
            self.assertEqual(result.orbits, 1)
            self.assertTrue(verify_orbit_certificate(size, pairs, result.certificate))
            if expected is not None:
                self.assertEqual(expected, result.certificate)
            expected = result.certificate

    def test_easy_mergers_and_no_mergers_do_not_build_an_adaptive_queue(self):
        for k in (1, 2, 12, 30):
            duplicate = IntervalPairing(0, 4, 5, 9)
            disjoint = [IntervalPairing(2*i, 2*i, 2*i + 1, 2*i + 1)
                        for i in range(k)]
            for pairs in ([duplicate] * k, disjoint):
                reference = restart_closure(pairs, merge=periodic_merge)
                adaptive = hybrid_closure(pairs, merge=periodic_merge)
                self.assertEqual(adaptive.pairings, reference.pairings)
                self.assertEqual(adaptive.pair_tests, reference.pair_tests)
                self.assertEqual(adaptive.queue_runs, 0)
                self.assertEqual(adaptive.peak_queue, 0)

    def test_first_pair_mergers_use_linear_eligibility_work(self):
        reads = 0

        class Row:
            @property
            def periodic(self):
                nonlocal reads
                reads += 1
                return True

        k = 256
        rows = [Row() for _ in range(k)]
        result = hybrid_closure(rows, merge=lambda left, right: left)
        self.assertEqual(result.pairings, rows[:1])
        self.assertEqual(result.pair_tests, k - 1)
        self.assertEqual(result.queue_runs, 0)
        # Guard the measured regression: collecting every eligible row at
        # every successful restart would make these reads quadratic in k.
        self.assertLessEqual(reads, 3 * k)

    def test_failed_first_candidate_is_not_retested_or_reordered(self):
        rows = [IntervalPairing(2*i, 2*i, 2*i + 1, 2*i + 1)
                if i % 2 == 0 else IntervalPairing(2*i, 2*i, 2*i, 2*i)
                for i in range(8)]
        calls = []

        def merge(left, right):
            calls.append((left, right))
            return periodic_merge(left, right)

        reference = restart_closure(rows, merge=merge)
        expected = list(calls)
        calls.clear()
        result = hybrid_closure(rows, merge=merge)
        self.assertEqual(calls, expected)
        self.assertEqual(result.pair_tests, reference.pair_tests)
        self.assertEqual(result.pairings, reference.pairings)
        self.assertEqual(result.queue_runs, 0)

    def test_stale_heap_entries_cannot_change_the_survivor_or_current_indices(self):
        rows = [IntervalPairing(0, 4, 5, 9)] * 10
        trace = []
        result = periodic_closure(rows, merge=periodic_merge, operations=trace)
        self.assertEqual(trace, [{'op': 'merge', 'left': 0, 'right': 1}] * 9)
        self.assertEqual(result.pairings, rows[:1])
        self.assertGreater(result.stale_pops, 0)
        self.assertEqual(rows, [rows[0]] * 10)

    def test_identity_reflection_and_empty_rows_are_filtered(self):
        for rows in ([], [IntervalPairing(0, 4, 0, 4)],
                     [IntervalPairing(0, 4, 0, 4, True)],
                     [IntervalPairing(0, 0, 0, 0, True)]):
            for closure in (periodic_closure, hybrid_closure):
                result = closure(rows, merge=periodic_merge)
                self.assertEqual(result.pairings, rows)
                self.assertEqual(result.pair_tests, 0)

    def test_cancellation_after_merger_propagates(self):
        for closure in (periodic_closure, hybrid_closure):
            trace = []

            def check():
                if trace:
                    raise RuntimeError('cancelled after the first merger')

            with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                closure([IntervalPairing(0, 3, 4, 7)] * 8,
                        merge=periodic_merge, operations=trace, check=check)
            self.assertEqual(len(trace), 1)

    def test_cycle_exhaustion_and_invalid_scheduler_values(self):
        size, pairs = five_cycle_system(8)
        for scheduler in ('legacy', 'adaptive', 'queue'):
            for allowance in (0, 4):
                result = count_orbits(size, pairs, merger_scheduler=scheduler,
                                      max_cycles=allowance, record_certificate=True)
                self.assertFalse(result.complete)
                self.assertIsNone(result.orbits)
                self.assertIsNone(result.certificate)
                self.assertEqual(result.cycles, allowance)
        for scheduler in (None, [], 1, True, 'automatic'):
            with self.assertRaises(ValueError):
                count_orbits(size, pairs, merger_scheduler=scheduler)


if __name__ == '__main__':
    unittest.main()
