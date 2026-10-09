"""Weighted interval orbits against literal finite equivalence relations."""

import copy
import random
import unittest
from collections import Counter

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.weighted_orbits import (
    weighted_histogram_from_orbit_certificate, weighted_orbit_histogram,
)
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


def literal_histogram(size, pairs, intervals, dimension):
    """Pointwise oracle, intentionally suitable only for small universes."""
    parents = list(range(size))

    def find(point):
        while point != parents[point]:
            parents[point] = parents[parents[point]]
            point = parents[point]
        return point

    for pair in pairs:
        for point in range(pair.a, pair.b + 1):
            parents[find(point)] = find(pair.image(point))
    values = [[0] * dimension for _ in range(size)]
    for lo, hi, value in intervals:
        for point in range(lo, hi):
            for j, entry in enumerate(value):
                values[point][j] += entry
    totals = {}
    for point, value in enumerate(values):
        total = totals.setdefault(find(point), [0] * dimension)
        for j, entry in enumerate(value):
            total[j] += entry
    return dict(Counter(tuple(value) for value in totals.values()))


def as_mapping(answer):
    return {tuple(row['weight']): row['orbits'] for row in answer['histogram']}


class WeightedOrbitsTests(unittest.TestCase):
    def checked(self, size, pairs, intervals, dimension=3, **options):
        answer = weighted_orbit_histogram(size, pairs, intervals, dimension=dimension,
                                          record_certificate=True, **options)
        self.assertEqual(answer['status'], 'COMPLETE')
        self.assertEqual(as_mapping(answer), literal_histogram(size, pairs, intervals, dimension))
        self.assertTrue(verify_weighted_orbit_certificate(
            size, pairs, intervals, answer['certificate'], dimension=dimension))
        stats = answer['stats']
        self.assertLessEqual(stats['maximum_weight_runs'], stats['input_weight_runs']
                             + 2 * (stats['translation_pushes'] + stats['reflection_pushes']))
        return answer

    def test_seeded_signed_vector_systems(self):
        randomizer = random.Random(73091)
        for case in range(1000):
            size = randomizer.randrange(61)
            pairs = []
            if size:
                for _ in range(randomizer.randrange(14)):
                    width = randomizer.randrange(1, size + 1)
                    a = randomizer.randrange(size - width + 1)
                    c = randomizer.randrange(size - width + 1)
                    pairs.append(IntervalPairing(a, a+width-1, c, c+width-1,
                                                bool(randomizer.randrange(2))))
            intervals = []
            for _ in range(randomizer.randrange(9)):
                lo = randomizer.randrange(size+1)
                hi = randomizer.randrange(lo, size+1)
                intervals.append((lo, hi, [randomizer.randrange(-4, 5) for _ in range(3)]))
            self.checked(size, pairs, intervals, periodic_rule='aht' if case & 1 else 'fine_wilf')

    def test_empty_universe_and_zero_weights(self):
        self.checked(0, [], [], max_cycles=0)
        self.checked(15, [], [])
        self.checked(15, [IntervalPairing(0, 10, 4, 14)], [])

    def test_static_gaps_and_overlapping_signed_intervals(self):
        self.checked(28, [IntervalPairing(3, 6, 20, 23)],
                     [(0, 28, (1, 2, -1)), (2, 25, (-1, -2, 1)),
                      (6, 9, (4, -7, 11)), (8, 8, (999, 0, 0))])

    def test_reflection_with_fixed_midpoint(self):
        for size in (17, 18):
            self.checked(size, [IntervalPairing(0, size-1, 0, size-1, True)],
                         [(0, 7, (1, 2, -3)), (4, 13, (5, -1, 7))])

    def test_nested_disjoint_transmissions(self):
        self.checked(55, [IntervalPairing(0, 12, 40, 52),
                          IntervalPairing(40, 43, 47, 50, True),
                          IntervalPairing(4, 5, 44, 45)],
                     [(0, 55, (1, 0, 1)), (42, 49, (-3, 7, 2))])

    def test_sharp_threshold_and_classical_rules_agree(self):
        pairs = [IntervalPairing(0, 12, 13, 25), IntervalPairing(2, 13, 14, 25)]
        intervals = [(0, 10, (1, 2, -1)), (7, 23, (-2, 1, 4))]
        sharp = self.checked(26, pairs, intervals)
        classical = self.checked(26, pairs, intervals, periodic_rule='aht')
        self.assertEqual(sharp['histogram'], classical['histogram'])

    def test_binary_size_and_large_signed_entries(self):
        size = 1 << 20000
        value = (1 << 500, -(1 << 999), 3)
        pairs = [IntervalPairing(0, size-2, 1, size-1)]
        intervals = [(0, size, value)]
        answer = weighted_orbit_histogram(size, pairs, intervals, record_certificate=True)
        self.assertEqual(answer['histogram'], [dict(weight=[entry*size for entry in value], orbits=1)])
        self.assertTrue(verify_weighted_orbit_certificate(
            hex(size), pairs, [(0, hex(size), [hex(entry) for entry in value])],
            json_safe(answer['certificate'])))

    def test_huge_reflection_has_known_two_point_orbits(self):
        size = 1 << 4096
        pairs = [IntervalPairing(0, size-1, 0, size-1, True)]
        answer = weighted_orbit_histogram(size, pairs, [(0, size, (1,))],
                                          record_certificate=True)
        self.assertEqual(answer['histogram'], [dict(weight=[2], orbits=size//2)])
        self.assertTrue(verify_weighted_orbit_certificate(
            size, pairs, [(0, size, (1,))], answer['certificate']))

    def test_supplied_trace_reuse(self):
        pairs = [IntervalPairing(0, 30, 5, 35)]
        weights = [(0, 36, (1, 0, 1)), (7, 22, (4, -5, 0))]
        proof = count_orbits(36, pairs, record_certificate=True).certificate
        answer = weighted_histogram_from_orbit_certificate(
            36, pairs, weights, proof, record_certificate=True)
        self.assertEqual(as_mapping(answer), literal_histogram(36, pairs, weights, 3))
        self.assertTrue(verify_weighted_orbit_certificate(36, pairs, weights, answer['certificate']))
        forged = copy.deepcopy(proof)
        forged['orbit_count'] += 1
        with self.assertRaises(ValueError):
            weighted_histogram_from_orbit_certificate(36, pairs, weights, forged)

    def test_incomplete_has_no_weight_claim(self):
        answer = weighted_orbit_histogram(4, [], [(0, 4, (1,))],
                                          max_cycles=0, record_certificate=True)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertNotIn('histogram', answer)
        self.assertNotIn('certificate', answer)

    def test_cancellation_propagates_in_producer_and_checker(self):
        class Stop(Exception):
            pass

        def stop():
            raise Stop('cooperative cancellation')

        with self.assertRaises(Stop):
            weighted_orbit_histogram(1, [], [(0, 1, (1,))], check=stop)
        answer = weighted_orbit_histogram(1, [], [(0, 1, (1,))], record_certificate=True)
        with self.assertRaises(Stop):
            verify_weighted_orbit_certificate(1, [], [(0, 1, (1,))],
                                               answer['certificate'], check=stop)
        with self.assertRaises(Stop):
            weighted_histogram_from_orbit_certificate(1, [], [(0, 1, (1,))],
                                                       answer['certificate']['orbit_proof'], check=stop)

    def test_input_validation(self):
        for size, intervals, dimension in (
                (-1, [], 1), (True, [], 1), (3, [(0, 4, [1])], 1),
                (3, [(2, 1, [1])], 1), (3, [(0, 1, [True])], 1),
                (3, [(0, 1, [1])], 2), (3, [], 0), (3, [], True)):
            with self.subTest(size=size, intervals=intervals, dimension=dimension):
                with self.assertRaises(ValueError):
                    weighted_orbit_histogram(size, [], intervals, dimension=dimension)
        with self.assertRaises(ValueError):
            weighted_orbit_histogram(3, [], [], record_certificate=1)

    def test_source_binding_and_histogram_mutation(self):
        pairs = [IntervalPairing(0, 6, 3, 9)]
        weights = [(0, 10, (1, 0, 3)), (2, 7, (-2, 1, 0))]
        answer = weighted_orbit_histogram(10, pairs, weights, record_certificate=True)
        certificate = answer['certificate']
        mutations = []
        for key, value in [('schema', 'wrong'), ('size', 9), ('dimension', 2)]:
            forged = copy.deepcopy(certificate)
            forged[key] = value
            mutations.append(forged)
        forged = copy.deepcopy(certificate)
        forged['histogram'][0]['orbits'] += 1
        mutations.append(forged)
        forged = copy.deepcopy(certificate)
        forged['histogram'][0]['weight'][0] += 1
        mutations.append(forged)
        forged = copy.deepcopy(certificate)
        forged['weights'][0][2][0] += 1
        mutations.append(forged)
        forged = copy.deepcopy(certificate)
        forged['orbit_proof']['operations'][-1]['gaps'][0][0] += 1
        mutations.append(forged)
        for forged in mutations:
            self.assertFalse(verify_weighted_orbit_certificate(10, pairs, weights, forged))
        self.assertFalse(verify_weighted_orbit_certificate(10, [], weights, certificate))
        self.assertFalse(verify_weighted_orbit_certificate(10, pairs, [(0, 10, (2, 0, 3))], certificate))


if __name__ == '__main__':
    unittest.main()
