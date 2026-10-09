"""Independent graph comparisons, arithmetic inflation, and replay attacks."""

from collections import Counter
from copy import deepcopy
from itertools import combinations_with_replacement, product
import random
import unittest
from unittest.mock import patch

from fastunknot.interval_orbits import IntervalPairing, count_orbits
try:
    import fastunknot.weighted_orbits as weighted
except ImportError:
    import weighted_orbits as weighted

WeightInterval = weighted.WeightInterval


def literal(size, pairs, marks, dimension):
    parent = list(range(size))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for p in pairs:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            parent[find(x)] = find(y)
    sums = {}
    for x in range(size):
        value = [0] * dimension
        for mark in marks:
            if mark.start <= x < mark.stop:
                value = [a + b for a, b in zip(value, mark.value)]
        component = sums.setdefault(find(x), [0] * dimension)
        for j, z in enumerate(value):
            component[j] += z
    return Counter(tuple(value) for value in sums.values())


def histogram(result):
    return Counter({row.value: row.multiplicity for row in result.classes})


def random_system(rng, n, maximum=8):
    result = []
    for _ in range(rng.randrange(maximum + 1)):
        width = rng.randint(1, n)
        a = rng.randint(0, n - width)
        c = rng.randint(0, n - width)
        result.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                      bool(rng.getrandbits(1))))
    return result


def random_marks(rng, n, dimension=3, maximum=8):
    result = []
    for _ in range(rng.randrange(maximum + 1)):
        a = rng.randrange(n)
        b = rng.randint(a + 1, n)
        value = tuple(rng.randint(-4, 4) for _ in range(dimension))
        result.append(WeightInterval(a, b, value))
    return result


class WeightedOrbitTests(unittest.TestCase):
    def assert_literal(self, n, pairs, marks, dimension, **kwargs):
        result = weighted.weighted_orbit_counts(n, pairs, marks,
                                                dimension=dimension, **kwargs)
        self.assertTrue(result.complete)
        self.assertEqual(histogram(result), literal(n, pairs, marks, dimension))
        self.assertEqual(sum(row.multiplicity for row in result.classes), result.orbits)
        if result.certificate is not None:
            self.assertTrue(weighted.verify_weighted_orbit_certificate(
                n, pairs, marks, result.certificate, dimension=dimension))
        return result

    def test_exhaustive_two_pairings_binary_point_weights(self):
        # Every pair of canonical interval isometries on n<=4, and every
        # 0/1-valued weight function; include the zero- and one-pair cases.
        for n in range(1, 5):
            pairs = []
            for width in range(1, n + 1):
                for a in range(n - width + 1):
                    for c in range(a, n - width + 1):
                        for reverse in (False, True):
                            pairs.append(IntervalPairing(a, a + width - 1,
                                                         c, c + width - 1, reverse))
            systems = [()] + [(p,) for p in pairs]
            systems.extend(combinations_with_replacement(pairs, 2))
            for point_weights in product((0, 1), repeat=n):
                marks = [WeightInterval(i, i + 1, (v,))
                         for i, v in enumerate(point_weights) if v]
                for system in systems:
                    self.assert_literal(n, system, marks, 1)

    def test_random_signed_vector_weights(self):
        rng = random.Random(2610097301)
        for case in range(2500):
            n = rng.randint(1, 45)
            pairs = random_system(rng, n)
            marks = random_marks(rng, n)
            self.assert_literal(n, pairs, marks, 3,
                                record_certificate=(case % 17 == 0))
            if case < 150:
                self.assert_literal(n, pairs, marks, 3, periodic_rule='aht')

    def test_full_range_folding_against_literal_push(self):
        rng = random.Random(2610097302)
        for _ in range(5000):
            n = rng.randint(2, 80)
            c = rng.randint(1, n - 1)
            a = rng.randrange(c)
            b = a + n - c - 1
            reverse = bool(rng.getrandbits(1)) and b < c
            p = [a, b, c, n - 1, -1 if reverse else 1]
            values = [tuple(rng.randint(-5, 5) for _ in range(2)) for _ in range(n)]
            # Occasionally use longer equal runs to make any breakpoint
            # growth visible; the oracle still iterates individual points.
            if rng.getrandbits(1):
                cuts = sorted(set([0, n] + [rng.randrange(n) for _ in range(5)]))
                for start, stop in zip(cuts, cuts[1:]):
                    values[start:stop] = [values[start]] * (stop - start)
            blocks = weighted._canonical(n,
                [(i, i + 1, value) for i, value in enumerate(values)], 2, lambda: None)
            new_size = rng.randint(c, n - 1)
            result = weighted._fold(blocks, p, n, new_size, 2, lambda: None)
            expected = [list(values[i]) if i < c else [0, 0]
                        for i in range(new_size)]
            for x in range(c, n):
                y = a + n - 1 - x if reverse else a + (x - a) % (c - a)
                for j in range(2):
                    expected[y][j] += values[x][j]
            actual = [value for lo, hi, value in result for _ in range(lo, hi)]
            self.assertEqual(actual, list(map(tuple, expected)))
            self.assertLessEqual(len(result) - len(blocks), 3)

    def test_three_run_growth_bound_is_sharp_in_complete_trace(self):
        pairs = [IntervalPairing(1, 2, 5, 6), IntervalPairing(3, 4, 4, 5),
                 IntervalPairing(0, 0, 3, 3)]
        marks = [WeightInterval(0, 7, (1,))]
        result = self.assert_literal(7, pairs, marks, 1, record_certificate=True)
        self.assertEqual(result.stats['initial_weight_blocks'], 1)
        self.assertEqual(result.stats['peak_weight_blocks'], 4)
        self.assertEqual(result.stats['max_transfer_block_growth'], 3)
        self.assertEqual(result.certificate['orbit_certificate']['operations'][0],
                         {'op': 'truncate', 'index': 0, 'new_size': 6})
        folded = weighted._fold([(0, 7, (1,))], [1, 2, 5, 6, 1],
                                 7, 6, 1, lambda: None)
        self.assertEqual(folded, [(0, 1, (1,)), (1, 3, (2,)),
                                  (3, 5, (1,)), (5, 6, (0,))])

    def test_enormous_period_and_enormous_orbits(self):
        period = 2 ** 4096 + 17
        quotient = 2 ** 8192 + 9
        remainder = 2 ** 1024 + 3
        n = quotient * period + remainder
        pairs = [IntervalPairing(0, n - period - 1, period, n - 1)]
        marks = [WeightInterval(0, n, (2, -3, 0))]
        result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=3,
                                                record_certificate=True)
        self.assertTrue(result.complete)
        expected = Counter({(2 * quotient, -3 * quotient, 0): period - remainder,
                            (2 * (quotient + 1), -3 * (quotient + 1), 0): remainder})
        self.assertEqual(histogram(result), expected)
        self.assertEqual(result.stats['weight_transfers'], 1)
        self.assertTrue(weighted.verify_weighted_orbit_certificate(
            n, pairs, marks, result.certificate, dimension=3))

    def test_enormous_reflection_and_parity(self):
        for n in (2 ** 9000, 2 ** 9000 + 1):
            pairs = [IntervalPairing(0, n - 1, 0, n - 1, True)]
            marks = [WeightInterval(0, n, (1,))]
            result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=1)
            expected = Counter({(2,): n // 2})
            if n % 2:
                expected[(1,)] = 1
            self.assertEqual(histogram(result), expected)

    def test_enormous_mark_boundaries_against_residue_counts(self):
        n, period = 2 ** 12000 + 35, 7
        pairs = [IntervalPairing(0, n - period - 1, period, n - 1)]
        marks = [WeightInterval(0, n, (1, 0, 0)),
                 WeightInterval(2 ** 9000 + 6, n - 9, (-2, 3, 0)),
                 WeightInterval(n // 3, n // 2 + 6, (0, -5, 17))]
        expected = Counter()
        for residue in range(period):
            value = [0, 0, 0]
            for mark in marks:
                count = ((mark.stop - 1 - residue) // period
                         - (mark.start - 1 - residue) // period)
                for j, coordinate in enumerate(mark.value):
                    value[j] += count * coordinate
            expected[tuple(value)] += 1
        result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=3)
        self.assertEqual(histogram(result), expected)

    def test_replay_has_no_orbit_search_dependency(self):
        n = 27
        pairs = [IntervalPairing(0, 21, 5, 26),
                 IntervalPairing(0, 19, 7, 26, True)]
        marks = [WeightInterval(2, 21, (1, 4)), WeightInterval(9, 25, (-3, 2))]
        result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=2,
                                                record_certificate=True)
        trace = result.certificate['orbit_certificate']
        with patch.object(weighted, 'count_orbits', side_effect=AssertionError('search')):
            self.assertTrue(weighted.verify_weighted_orbit_certificate(
                n, pairs, marks, result.certificate, dimension=2))
            replay = weighted.replay_weighted_orbits(n, pairs, marks, trace, dimension=2)
        self.assertTrue(replay.complete)
        self.assertEqual(replay.classes, result.classes)
        self.assertEqual(replay.cycles, 0)

    def test_certificate_mutations_and_source_binding(self):
        n = 12
        pairs = [IntervalPairing(0, 3, 4, 7), IntervalPairing(4, 7, 8, 11)]
        marks = [WeightInterval(0, 4, (1, 0)), WeightInterval(2, 11, (0, -1))]
        result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=2,
                                                record_certificate=True)
        good = result.certificate
        mutations = []
        bad = deepcopy(good); bad['classes'][0][0][0] += 1; mutations.append(bad)
        bad = deepcopy(good); bad['classes'][0][1] += 1; mutations.append(bad)
        bad = deepcopy(good); bad['classes'][0][1] = True; mutations.append(bad)
        bad = deepcopy(good); bad['dimension'] = True; mutations.append(bad)
        bad = deepcopy(good); bad['weights'][0][2][0] += 1; mutations.append(bad)
        bad = deepcopy(good); bad['weights'][0][0] = True; mutations.append(bad)
        bad = deepcopy(good); bad['unexpected'] = 0; mutations.append(bad)
        bad = deepcopy(good); bad['orbit_certificate']['operations'].pop(); mutations.append(bad)
        bad = deepcopy(good); bad['orbit_certificate']['version'] = 1; mutations.append(bad)
        bad = deepcopy(good); bad['orbit_certificate']['pairings'][0][4] = -1; mutations.append(bad)
        for bad in mutations:
            self.assertFalse(weighted.verify_weighted_orbit_certificate(
                n, pairs, marks, bad, dimension=2))
        other_marks = marks + [WeightInterval(11, 12, (1, 0))]
        self.assertFalse(weighted.verify_weighted_orbit_certificate(
            n, pairs, other_marks, good, dimension=2))
        self.assertFalse(weighted.verify_weighted_orbit_certificate(
            n, list(reversed(pairs)), marks, good, dimension=2))
        self.assertEqual(good, result.certificate)

    def test_hexadecimal_serialization(self):
        from fastunknot.integer_codec import json_safe
        n = 2 ** 18000 + 9
        pairs = [IntervalPairing(0, n - 8, 7, n - 1)]
        marks = [WeightInterval(0, n, (1, -2))]
        result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=2,
                                                record_certificate=True)
        self.assertTrue(weighted.verify_weighted_orbit_certificate(
            n, pairs, marks, json_safe(result.certificate), dimension=2))

    def test_zero_universe_and_zero_weights(self):
        result = weighted.weighted_orbit_counts(0, [], [], dimension=4,
                                                record_certificate=True)
        self.assertEqual(result.classes, ())
        self.assertEqual(result.aggregate, (0, 0, 0, 0))
        self.assertTrue(weighted.verify_weighted_orbit_certificate(
            0, [], [], result.certificate, dimension=4))
        n = 2 ** 8000
        result = weighted.weighted_orbit_counts(n, [], [], dimension=2)
        self.assertEqual(histogram(result), {(0, 0): n})

    def test_zero_dimensional_weight_vectors(self):
        for n, pairs in ((0, []), (17, []),
                         (17, [IntervalPairing(0, 11, 5, 16)])):
            marks = [WeightInterval(0, n, ())] if n else []
            result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=0,
                                                    record_certificate=True)
            self.assertTrue(result.complete)
            self.assertEqual(result.aggregate, ())
            self.assertEqual(result.orbits, count_orbits(n, pairs).orbits)
            expected = () if not n else (weighted.WeightedOrbitClass((), result.orbits),)
            self.assertEqual(result.classes, expected)
            self.assertTrue(weighted.verify_weighted_orbit_certificate(
                n, pairs, marks, result.certificate, dimension=0))

    def test_limits_fail_closed(self):
        n = 10
        pairs = [IntervalPairing(0, 6, 3, 9)]
        marks = [WeightInterval(0, 5, (1,)), WeightInterval(2, 9, (-2,))]
        for limits in ({'max_cycles': 0}, {'max_operations': 0},
                       {'max_weight_blocks': 1}, {'max_output_records': 1}):
            result = weighted.weighted_orbit_counts(n, pairs, marks, dimension=1,
                                                    record_certificate=True, **limits)
            self.assertFalse(result.complete)
            self.assertIsNone(result.classes)
            self.assertIsNone(result.aggregate)
            self.assertIsNone(result.orbits)
            self.assertIsNone(result.certificate)
        complete = weighted.weighted_orbit_counts(n, pairs, marks, dimension=1,
                                                  record_certificate=True)
        self.assertFalse(weighted.verify_weighted_orbit_certificate(
            n, pairs, marks, complete.certificate, dimension=1, max_operations=0))
        exact = weighted.weighted_orbit_counts(n, pairs, marks, dimension=1,
             max_cycles=complete.cycles,
             max_operations=complete.stats['replayed_events'],
             max_weight_blocks=complete.stats['peak_weight_blocks'],
             max_output_records=len(complete.classes))
        self.assertTrue(exact.complete)

    def test_strict_validation_and_cancellation(self):
        for args in ((True, 3, (1,)), (0, True, (1,)), (0, 0, (1,)),
                     (0, 1, (True,)), (0, 1, [1])):
            with self.assertRaises(ValueError):
                WeightInterval(*args)
        for args in ((1, [], [], -1), (True, [], [], 1),
                     (1, [], [WeightInterval(0, 2, (1,))], 1),
                     (2, [], [WeightInterval(0, 1, (1, 2))], 1)):
            n, pairs, marks, dimension = args
            with self.assertRaises(ValueError):
                weighted.weighted_orbit_counts(n, pairs, marks, dimension=dimension)
        for limit in (True, -1, '2'):
            with self.assertRaises(ValueError):
                weighted.weighted_orbit_counts(1, [], [], dimension=1,
                                                max_operations=limit)
        class Cancel(ValueError):
            pass
        def abort():
            raise Cancel('cancelled')
        with self.assertRaises(Cancel):
            weighted.weighted_orbit_counts(1, [], [], dimension=1, check=abort)
        result = weighted.weighted_orbit_counts(1, [], [], dimension=1,
                                                record_certificate=True)
        with self.assertRaises(Cancel):
            weighted.verify_weighted_orbit_certificate(
                1, [], [], result.certificate, dimension=1, check=abort)


if __name__ == '__main__':
    unittest.main()
