"""Least orbit representatives: explicit oracles, huge inputs and hostile proofs."""

import copy
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.orbit_transversal import (
    orbit_transversal, transversal_from_orbit_certificate,
)
from fastunknot.orbit_transversal_verify import verify_orbit_transversal_certificate
from fastunknot.weighted_orbits import weighted_orbit_histogram


def literal_least_points(size, pairings):
    """Independent pointwise oracle, used only on bounded finite systems."""
    parent = list(range(size))

    def root(point):
        while parent[point] != point:
            parent[point] = parent[parent[point]]
            point = parent[point]
        return point

    for pairing in pairings:
        for point in range(pairing.a, pairing.b + 1):
            left, right = root(point), root(pairing.image(point))
            parent[max(left, right)] = min(left, right)
    return {point for point in range(size) if root(point) == point}


def expanded(intervals):
    return {point for lo, hi in intervals for point in range(lo, hi)}


class OrbitTransversalTests(unittest.TestCase):
    def checked(self, size, pairings, **options):
        answer = orbit_transversal(size, pairings, record_certificate=True, **options)
        self.assertEqual(answer['status'], 'COMPLETE')
        expected = literal_least_points(size, pairings)
        self.assertEqual(expanded(answer['representative_intervals']), expected)
        self.assertEqual(answer['orbit_count'], len(expected))
        self.assertTrue(verify_orbit_transversal_certificate(
            size, pairings, answer['certificate']))
        self.assertLessEqual(len(answer['representative_intervals']),
                             answer['stats']['contraction_gap_intervals'])
        return answer

    def test_seeded_systems_and_scheduler_independence(self):
        randomizer = random.Random(910261)
        for _ in range(750):
            size = randomizer.randrange(75)
            pairings = []
            if size:
                for _ in range(randomizer.randrange(18)):
                    width = randomizer.randrange(1, size + 1)
                    a = randomizer.randrange(size - width + 1)
                    c = randomizer.randrange(size - width + 1)
                    pairings.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                                   bool(randomizer.randrange(2))))
            left = self.checked(size, pairings, periodic_rule='fine_wilf')
            right = self.checked(size, pairings, periodic_rule='aht')
            self.assertEqual(left['representative_intervals'], right['representative_intervals'])

    def test_empty_universe_and_static_points(self):
        empty = self.checked(0, [], max_cycles=0)
        self.assertEqual(empty['representative_intervals'], [])
        static = self.checked(19, [])
        self.assertEqual(static['representative_intervals'], [[0, 19]])

    def test_fixed_reflection_midpoints_and_identity(self):
        for size in (1, 2, 17, 18, 31):
            result = self.checked(size, [IntervalPairing(0, size - 1, 0, size - 1, True),
                                         IntervalPairing(0, size - 1, 0, size - 1)])
            self.assertEqual(result['representative_intervals'], [[0, (size + 1) // 2]])

    def test_static_gaps_preserve_original_labels(self):
        pairings = [IntervalPairing(3, 6, 20, 23),
                    IntervalPairing(4, 5, 26, 27, True)]
        self.checked(32, pairings)

    def test_nested_transmissions_and_truncations(self):
        pairings = [IntervalPairing(0, 12, 40, 52),
                    IntervalPairing(40, 43, 47, 50, True),
                    IntervalPairing(4, 5, 44, 45)]
        answer = self.checked(55, pairings)
        operations = answer['certificate']['orbit_proof']['operations']
        self.assertTrue(any(event['op'] == 'transmit' for event in operations))
        self.assertTrue(any(event['op'] == 'truncate' for event in operations))

    def test_huge_translation_fibres_never_expand(self):
        period = (1 << 20000) + 17
        blocks = 29
        size = blocks * period
        pairings = [IntervalPairing(i * period, (i + 1) * period - 1,
                                   (i + 1) * period, (i + 2) * period - 1)
                    for i in range(blocks - 1)]
        answer = orbit_transversal(size, pairings, record_certificate=True)
        self.assertEqual(answer['representative_intervals'], [[0, period]])
        self.assertEqual(answer['orbit_count'], period)
        self.assertLess(answer['stats']['trace_events'], 100)
        self.assertTrue(verify_orbit_transversal_certificate(
            size, pairings, json_safe(answer['certificate'])))

    def test_huge_reflection_and_disconnected_gaps(self):
        block = (1 << 16000) + 19
        size = 5 * block
        pairings = [IntervalPairing(block, 2 * block - 1, 3 * block, 4 * block - 1, True)]
        answer = orbit_transversal(size, pairings, record_certificate=True)
        self.assertEqual(answer['representative_intervals'], [[0, 3 * block], [4 * block, size]])
        self.assertTrue(verify_orbit_transversal_certificate(size, pairings, answer['certificate']))

    def test_nested_component_counts_without_refinement_expansion(self):
        block = (1 << 18000) + 23
        fine = [IntervalPairing(0, block - 1, block, 2 * block - 1)]
        coarse = fine + [IntervalPairing(0, 2 * block - 1, 2 * block, 4 * block - 1)]
        selector = orbit_transversal(4 * block, fine, record_certificate=True)
        self.assertEqual(selector['representative_intervals'], [[0, block], [2 * block, 4 * block]])
        intervals = [(lo, hi, [1]) for lo, hi in selector['representative_intervals']]
        census = weighted_orbit_histogram(4 * block, coarse, intervals, dimension=1)
        self.assertEqual(census['histogram'], [dict(weight=[3], orbits=block)])

    def test_equal_cardinality_alternative_representatives_rejected(self):
        pairings = [IntervalPairing(0, 11, 12, 23)]
        proof = orbit_transversal(24, pairings, record_certificate=True)['certificate']
        changed = copy.deepcopy(proof)
        changed['representative_intervals'] = [[12, 24]]
        # This IS an orbit transversal, but the certificate promises least
        # original representatives, so equal cardinality is insufficient.
        self.assertFalse(verify_orbit_transversal_certificate(24, pairings, changed))

    def test_reuse_and_independent_replay_with_producer_disabled(self):
        pairings = [IntervalPairing(3, 11, 30, 38, True)]
        trace = count_orbits(43, pairings, record_certificate=True).certificate
        with patch('fastunknot.orbit_transversal.count_orbits', side_effect=AssertionError):
            answer = transversal_from_orbit_certificate(
                43, pairings, trace, record_certificate=True)
        with patch('fastunknot.orbit_transversal._forward_selector', side_effect=AssertionError), \
                patch('fastunknot.orbit_transversal.count_orbits', side_effect=AssertionError), \
                patch('fastunknot.interval_orbits.count_orbits', side_effect=AssertionError):
            self.assertTrue(verify_orbit_transversal_certificate(
                43, pairings, answer['certificate']))

    def test_source_and_result_mutations_are_rejected(self):
        pairings = [IntervalPairing(3, 11, 30, 38, True)]
        answer = self.checked(43, pairings)
        proof = answer['certificate']
        mutations = []
        for field, value in [('size', 44), ('orbit_count', answer['orbit_count'] + 1),
                             ('schema', 'unknown'), ('representative_intervals', [])]:
            changed = copy.deepcopy(proof)
            changed[field] = value
            mutations.append(changed)
        changed = copy.deepcopy(proof)
        changed['representative_intervals'][0][0] = 1
        mutations.append(changed)
        changed = copy.deepcopy(proof)
        changed['representative_intervals'] = list(reversed(changed['representative_intervals']))
        mutations.append(changed)
        changed = copy.deepcopy(proof)
        changed['orbit_proof']['operations'] = changed['orbit_proof']['operations'][:-1]
        mutations.append(changed)
        changed = copy.deepcopy(proof)
        changed['orbit_proof']['pairings'][0][0] += 1
        mutations.append(changed)
        for changed in mutations:
            self.assertFalse(verify_orbit_transversal_certificate(43, pairings, changed))
        foreign = [IntervalPairing(3, 11, 29, 37, True)]
        self.assertFalse(verify_orbit_transversal_certificate(43, foreign, proof))
        with self.assertRaises(ValueError):
            transversal_from_orbit_certificate(43, foreign, proof['orbit_proof'])

    def test_noncanonical_types_and_adjacent_split_rejected(self):
        proof = orbit_transversal(12, [], record_certificate=True)['certificate']
        for intervals in ([[0, 6], [6, 12]], [[0, 12], [0, 12]], [[True, 12]],
                          [[0, 12.0]], [[-1, 12]], [[0, 13]], [[0, 0]], 'bad'):
            changed = copy.deepcopy(proof)
            changed['representative_intervals'] = intervals
            self.assertFalse(verify_orbit_transversal_certificate(12, [], changed))
        for field in ('size', 'orbit_count'):
            changed = copy.deepcopy(proof)
            changed[field] = True
            self.assertFalse(verify_orbit_transversal_certificate(12, [], changed))

    def test_inconclusive_has_no_partial_answer(self):
        answer = orbit_transversal(20, [IntervalPairing(0, 7, 10, 17)], max_cycles=0,
                                   record_certificate=True)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        for field in ('orbit_count', 'representative_intervals', 'certificate'):
            self.assertNotIn(field, answer)
        for options in ({'max_cycles': -1}, {'max_cycles': True},
                        {'periodic_rule': 'unknown'}, {'record_certificate': 1}):
            with self.assertRaises(ValueError):
                orbit_transversal(0, [], **options)

    def test_false_valued_callbacks_and_late_cancellation(self):
        class Cancelled(Exception):
            pass

        class Callback:
            def __init__(self, trigger):
                self.calls = 0
                self.trigger = trigger

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == self.trigger:
                    raise Cancelled

        pairings = [IntervalPairing(3, 11, 30, 38, True)]
        trace = count_orbits(43, pairings, record_certificate=True).certificate
        proof = transversal_from_orbit_certificate(
            43, pairings, trace, record_certificate=True)['certificate']
        for call in (lambda check: orbit_transversal(43, pairings, check=check),
                     lambda check: transversal_from_orbit_certificate(43, pairings, trace,
                                                                       check=check),
                     lambda check: verify_orbit_transversal_certificate(43, pairings, proof,
                                                                        check=check)):
            counter = Callback(10 ** 9)
            call(counter)
            self.assertGreater(counter.calls, 5)
            for trigger in (1, counter.calls - 1):
                with self.assertRaises(Cancelled):
                    call(Callback(trigger))


if __name__ == '__main__':
    unittest.main()
