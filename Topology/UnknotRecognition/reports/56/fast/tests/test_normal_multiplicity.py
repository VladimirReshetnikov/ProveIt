"""Exact common-multiplicity reduction, one-sided lifting and v1 compatibility."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import _TOPOLOGY_FIELDS
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.fixtures import layered_torus


def topology(result):
    return {key: result[key] for key in _TOPOLOGY_FIELDS if key in result}


class NormalMultiplicityTests(unittest.TestCase):
    def test_small_scalings_two_sided_one_sided_and_mixed(self):
        tri, disk = layered_torus(1)
        for base in (disk, [[0, 0, 0, 0, 0, 1, 0]], [[1, 1, 1, 1, 0, 1, 0]]):
            primitive = normal_surface_topology(tri, base)
            for k in range(1, 10):
                vector = [[k * value for value in row] for row in base]
                old = normal_surface_topology(tri, vector, record_certificate=True, reduce_multiplicity=False)
                current = normal_surface_topology(tri, vector, record_certificate=True)
                self.assertEqual(topology(old), topology(current))
                o, n = primitive['orientable_components'], primitive['nonorientable_components']
                self.assertEqual(current['orientable_components'], k * o + (k // 2) * n)
                self.assertEqual(current['nonorientable_components'], (k % 2) * n)
                self.assertEqual(current['boundary_components'], k * primitive['boundary_components'])
                self.assertEqual(current['euler_characteristic'], k * primitive['euler_characteristic'])
                for result in (old, current):
                    self.assertTrue(verify_normal_surface_certificate(tri, vector, result['certificate']))
                if k > 1:
                    self.assertEqual(current['coordinate_divisor'], k)
                    self.assertEqual(current['queries'], primitive['queries'])
                    self.assertEqual(current['certificate']['schema'], 'normal-surface-topology-v2')
                else:
                    self.assertEqual(old, current)
                self.assertEqual(old['certificate']['schema'], 'normal-surface-topology-v1')

    def test_huge_binary_scaling_preserves_original_claims_and_small_queries(self):
        tri, disk = layered_torus(8)
        for factor in (2**20000, 2**20000 + 1):
            vector = [[factor * value for value in row] for row in disk]
            new = normal_surface_topology(tri, vector, record_certificate=True)
            old = normal_surface_topology(tri, vector, record_certificate=True, reduce_multiplicity=False)
            self.assertEqual(topology(new), topology(old))
            self.assertGreater(new['maximum_coordinate_bits'], 20000)
            self.assertLess(new['queries']['surface']['stats']['input_bits'], 20)
            self.assertGreater(old['queries']['surface']['stats']['input_bits'], 20000)
            encoded = json.loads(json.dumps(json_safe(new['certificate'])))
            self.assertTrue(verify_normal_surface_certificate(tri, vector, encoded))
            self.assertLess(len(json.dumps(json_safe(new['certificate']))),
                            len(json.dumps(json_safe(old['certificate']))) // 5)

    def test_empty_and_primitive_keep_version_one_and_exact_result(self):
        tri, vector = layered_torus(4)
        for coords in (vector, [[0] * 7 for _ in vector]):
            enabled = normal_surface_topology(tri, coords, record_certificate=True)
            disabled = normal_surface_topology(tri, coords, record_certificate=True, reduce_multiplicity=False)
            self.assertEqual(enabled, disabled)
            self.assertEqual(enabled['certificate']['schema'], 'normal-surface-topology-v1')

    def test_divisor_schema_and_foreign_quotient_forgery(self):
        tri, base = layered_torus(4)
        vector = [[12 * value for value in row] for row in base]
        proof = normal_surface_topology(tri, vector, record_certificate=True)['certificate']
        for divisor in (0, 1, -12, True, 12.0, 5, 6, None, '12'):
            forged = deepcopy(proof); forged['coordinate_divisor'] = divisor
            self.assertFalse(verify_normal_surface_certificate(tri, vector, forged), divisor)
        forged = deepcopy(proof); del forged['coordinate_divisor']
        self.assertFalse(verify_normal_surface_certificate(tri, vector, forged))
        forged = deepcopy(proof); forged['schema'] = 'normal-surface-topology-v1'
        self.assertFalse(verify_normal_surface_certificate(tri, vector, forged))
        del forged['coordinate_divisor']
        self.assertFalse(verify_normal_surface_certificate(tri, vector, forged))
        # A proper common divisor is sound if its quotient's complete proof is supplied.
        quotient = [[2 * value for value in row] for row in base]
        alternate = normal_surface_topology(tri, quotient, record_certificate=True,
                                            reduce_multiplicity=False)['certificate']
        forged = deepcopy(proof); forged['coordinate_divisor'] = 6
        forged['queries'] = alternate['queries']
        self.assertTrue(verify_normal_surface_certificate(tri, vector, forged))
        # Even a rewritten source digest must not turn zero into a scaled proof.
        empty = [[0] * 7 for _ in base]
        zero = normal_surface_topology(tri, empty, record_certificate=True)['certificate']
        zero.update(schema='normal-surface-topology-v2', coordinate_divisor=12)
        self.assertFalse(verify_normal_surface_certificate(tri, empty, zero))

    def test_original_boundary_parity_not_quotient_parity(self):
        tri, disk = layered_torus(1)
        vector = [[2 * value for value in row] for row in disk]
        proof = normal_surface_topology(tri, vector, record_certificate=True)['certificate']
        self.assertFalse(proof['boundary_homology']['nonzero'])
        forged = deepcopy(proof)
        forged['boundary_homology'] = normal_surface_topology(tri, disk,
                                            record_certificate=True)['certificate']['boundary_homology']
        self.assertFalse(verify_normal_surface_certificate(tri, vector, forged))

    def test_one_sided_even_multiple_is_connected_orientable_annulus(self):
        tri, _ = layered_torus(1)
        result = normal_surface_topology(tri, [[0, 0, 0, 0, 0, 2, 0]], record_certificate=True)
        self.assertEqual((result['components'], result['orientable_components'],
                          result['nonorientable_components'], result['boundary_components'],
                          result['genus']), (1, 1, 0, 2, 0))
        self.assertNotIn('crosscaps', result)
        self.assertFalse(result['compressing_disk'])

    def test_shared_caps_and_cancellation_during_division(self):
        tri, base = layered_torus(5)
        vector = [[64 * value for value in row] for row in base]
        full = normal_surface_topology(tri, vector, record_certificate=True)
        for cap in (0, full['cycles'] - 1):
            result = normal_surface_topology(tri, vector, record_certificate=True, max_cycles=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
            self.assertNotIn('components', result)
            self.assertEqual(result['coordinate_divisor'], 64)
        exact = normal_surface_topology(tri, vector, record_certificate=True, max_cycles=full['cycles'])
        self.assertEqual(exact, full)
        events = sum(len(q['operations']) for q in full['certificate']['queries'].values())
        self.assertTrue(verify_normal_surface_certificate(tri, vector, full['certificate'], max_operations=events))
        self.assertFalse(verify_normal_surface_certificate(tri, vector, full['certificate'], max_operations=events-1))
        # An external ValueError must escape even from quotient construction.
        from fastunknot.normal_surface_geometry import _divide_coordinates
        def interrupted(analysed, divisor, check):
            def fail(): raise ValueError('cancel division')
            return _divide_coordinates(analysed, divisor, fail)
        with patch('fastunknot.normal_surface_verify._divide_coordinates', interrupted):
            with self.assertRaisesRegex(ValueError, 'cancel division'):
                verify_normal_surface_certificate(tri, vector, full['certificate'])
        with self.assertRaises(ValueError):
            normal_surface_topology(tri, vector, reduce_multiplicity=1)

    def test_replay_does_not_recompute_gcd_or_orbit_search(self):
        tri, vector = layered_torus(4)
        vector = [[120 * value for value in row] for row in vector]
        proof = normal_surface_topology(tri, vector, record_certificate=True)['certificate']
        with patch('fastunknot.normal_surface_orbits._primitive_coordinates', side_effect=AssertionError), \
             patch('fastunknot.normal_surface_orbits.count_orbits', side_effect=AssertionError):
            self.assertTrue(verify_normal_surface_certificate(tri, vector, proof))


if __name__ == '__main__':
    unittest.main()
