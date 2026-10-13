"""Conservation is complete only after independently proving one orbit."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.weighted_orbits import weighted_orbit_histogram, weighted_histogram_from_orbit_certificate
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


class SingleOrbitWeightTests(unittest.TestCase):
    def test_binary_signed_mass_replays_without_weight_transport(self):
        n = 1 << 20000
        pairs = [IntervalPairing(0, n-2, 1, n-1)]
        weights = [(0, n, [3, -5, 0]), (3, n-1, [-7, 11, 1])]
        expected = [3*n-7*(n-4), -5*n+11*(n-4), n-4]
        with patch('fastunknot.weighted_orbits._replay', side_effect=AssertionError):
            result = weighted_orbit_histogram(n, pairs, weights, record_certificate=True)
        self.assertEqual(result['histogram'], [dict(weight=expected, orbits=1)])
        self.assertEqual(result['stats']['single_orbit_shortcut'], 1)
        proof = json.loads(json.dumps(json_safe(result['certificate'])))
        with patch('fastunknot.weighted_orbit_verify._replay', side_effect=AssertionError), \
             patch('fastunknot.weighted_orbits.weighted_orbit_histogram', side_effect=AssertionError):
            self.assertTrue(verify_weighted_orbit_certificate(n, pairs, weights, proof))
        with patch('fastunknot.weighted_orbits._replay', side_effect=AssertionError):
            reused = weighted_histogram_from_orbit_certificate(n, pairs, weights,
                        result['certificate']['orbit_proof'], record_certificate=True)
        self.assertEqual(reused['certificate'], result['certificate'])

    def test_equal_total_mass_does_not_certify_multiple_orbit_weights(self):
        pairs = [IntervalPairing(0, 0, 2, 2), IntervalPairing(1, 1, 3, 3)]
        weights = [(i, i+1, [i+1]) for i in range(4)]
        result = weighted_orbit_histogram(4, pairs, weights, record_certificate=True)
        self.assertEqual(result['histogram'], [dict(weight=[4], orbits=1), dict(weight=[6], orbits=1)])
        self.assertEqual(result['stats']['single_orbit_shortcut'], 0)
        forged = deepcopy(result['certificate'])
        forged['histogram'] = [dict(weight=[5], orbits=2)]
        self.assertFalse(verify_weighted_orbit_certificate(4, pairs, weights, forged))
        forged['orbit_proof']['orbit_count'] = 1
        forged['histogram'] = [dict(weight=[10], orbits=1)]
        self.assertFalse(verify_weighted_orbit_certificate(4, pairs, weights, forged))
        with self.assertRaises(ValueError):
            weighted_histogram_from_orbit_certificate(4, pairs, weights, forged['orbit_proof'])

    def test_single_orbit_proof_operations_and_weight_binding_remain_checked(self):
        pairs = [IntervalPairing(0, 14, 1, 15)]
        weights = [(0, 16, [1, -2])]
        proof = weighted_orbit_histogram(16, pairs, weights, record_certificate=True)['certificate']
        for field in ('weights', 'histogram', 'orbit_proof'):
            bad = deepcopy(proof)
            if field == 'weights': bad[field][0][2][0] += 1
            elif field == 'histogram': bad[field][0]['weight'][0] += 1
            else: bad[field]['operations'] = []
            self.assertFalse(verify_weighted_orbit_certificate(16, pairs, weights, bad))
        bad = deepcopy(proof); bad['orbit_proof']['orbit_count'] = True
        self.assertFalse(verify_weighted_orbit_certificate(16, pairs, weights, bad))
        self.assertFalse(verify_weighted_orbit_certificate(16, [], weights, proof))
        stopped = []
        def cancel():
            stopped.append(1)
            if len(stopped) == 10:
                raise RuntimeError('cancel mass proof')
        with self.assertRaisesRegex(RuntimeError, 'cancel mass proof'):
            verify_weighted_orbit_certificate(16, pairs, weights, proof, check=cancel)

    def test_empty_and_singleton_universes(self):
        for size, intervals, histogram in ((0, [], []), (1, [], [dict(weight=[0], orbits=1)]),
                                           (1, [(0, 1, [-3])], [dict(weight=[-3], orbits=1)])):
            result = weighted_orbit_histogram(size, [], intervals, record_certificate=True)
            self.assertEqual(result['histogram'], histogram)
            self.assertTrue(verify_weighted_orbit_certificate(size, [], intervals, result['certificate']))
            self.assertEqual(result['stats']['single_orbit_shortcut'], int(size == 1))


if __name__ == '__main__':
    unittest.main()
