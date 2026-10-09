"""Linear ray gates: exact closures, forced fallback and independent replay."""

from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.normal_support import compile_support
from fastunknot.normal_support_peeling import peel_support_ray, peel_normal_support_ray
from fastunknot.normal_support_peeling_verify import verify_support_ray, verify_normal_support_ray
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from normal_orbit_research.fixtures import layered_torus, boundary_cap
from tests.test_normal_support import algebra_fixture


class NormalSupportPeelingTests(unittest.TestCase):
    def test_layered_family_exact_linear_transcripts(self):
        for size in (1, 2, 3, 8, 32, 128, 256):
            tri, coordinates = layered_torus(size)
            proof = peel_normal_support_ray(tri, coordinates)
            self.assertIsNotNone(proof)
            self.assertEqual(proof['seed'], 0 if size == 1 else 7 * (size - 2) + 6)
            self.assertEqual(len(proof['steps']), 3 * size - 1)
            self.assertTrue(verify_normal_support_ray(tri, coordinates, proof))

    def test_constant_incidence_work_and_caps(self):
        recorded = []
        for size in (8, 16, 32, 64, 128):
            tri, coordinates = layered_torus(size)
            prepared = _prepare(tri, lambda: None)
            analysed = _coordinates(prepared, coordinates, lambda: None)
            count = [0]

            def tick():
                count[0] += 1

            proof = peel_support_ray(prepared, analysed, tick)
            recorded.append(count[0])
            self.assertLessEqual(count[0], 40 * size)
            self.assertTrue(verify_support_ray(prepared, analysed, proof))
        self.assertTrue(all(b < 3 * a for a, b in zip(recorded, recorded[1:])))
        tri, coordinates = layered_torus(5)
        for _ in range(3):
            tri, coordinates = boundary_cap(tri, coordinates)
            proof = peel_normal_support_ray(tri, coordinates)
            self.assertTrue(verify_normal_support_ray(tri, coordinates, proof))

    def test_rank_one_can_fail_exposure_and_empty_is_not_a_ray(self):
        prepared, analysed = algebra_fixture()
        self.assertEqual(compile_support(prepared, analysed)['nullity'], 1)
        self.assertIsNone(peel_support_ray(prepared, analysed))
        tri, coordinates = layered_torus(2)
        empty = [[0] * 7 for _ in coordinates]
        self.assertIsNone(peel_normal_support_ray(tri, empty))
        false = dict(schema='normal-support-ray-peeling-v1', support=[], seed=0, steps=[], nullity=1)
        self.assertFalse(verify_normal_support_ray(tri, empty, false))
        independent = {'matching': []}
        self.assertIsNone(peel_support_ray(independent, {'rows': [[1, 1, 0, 0, 0, 0, 0]]}))
        single = {'rows': [[0, 0, 3, 0, 0, 0, 0]]}
        proof = peel_support_ray(independent, single)
        self.assertEqual(proof['steps'], [])
        self.assertTrue(verify_support_ray(independent, single, proof))

    def test_unit_pivots_certify_the_seed_gcd(self):
        from math import gcd
        for size in (1, 2, 8, 32):
            tri, coordinates = layered_torus(size)
            scale = (1 << 5000) + 1
            coordinates = [[value * scale for value in row] for row in coordinates]
            proof = peel_normal_support_ray(tri, coordinates)
            flat = sum(coordinates, [])
            self.assertEqual(flat[proof['seed']], gcd(*flat))
        prepared = {'matching': [{0: 3, 1: -2}]}
        source = {'rows': [[2, 3, 0, 0, 0, 0, 0]]}
        self.assertIsNone(peel_support_ray(prepared, source))
        false = dict(schema='normal-support-ray-peeling-v1', support=[0, 1],
                     seed=0, steps=[[0, 1]], nullity=1)
        self.assertFalse(verify_support_ray(prepared, source, false))
        prepared = {'matching': [{0: 2, 1: -1}]}
        source = {'rows': [[1, 2, 0, 0, 0, 0, 0]]}
        proof = peel_support_ray(prepared, source)
        self.assertTrue(verify_support_ray(prepared, source, proof))
        false = dict(schema='normal-support-ray-peeling-v1', support=[0, 1],
                     seed=1, steps=[[0, 0]], nullity=1)
        self.assertFalse(verify_support_ray(prepared, source, false))

    def test_hex_reuse_independent_checker_and_forged_rows(self):
        tri, coordinates = layered_torus(11)
        proof = peel_normal_support_ray(tri, coordinates)
        huge = [[hex(((1 << 5000) + 1) * value) for value in row] for row in coordinates]
        self.assertTrue(verify_normal_support_ray(tri, huge, proof))
        encoded = deepcopy(proof)
        encoded['support'] = [hex(i) for i in proof['support']]
        encoded['steps'] = [[hex(value) for value in row] for row in proof['steps']]
        encoded['seed'], encoded['nullity'] = hex(proof['seed']), '0x1'
        with patch('fastunknot.normal_support_peeling.peel_support_ray', side_effect=AssertionError), \
             patch('fastunknot.normal_support.compile_support', side_effect=AssertionError):
            self.assertTrue(verify_normal_support_ray(tri, huge, encoded))
        for field, value in (('seed', True), ('seed', -1), ('nullity', True),
                             ('steps', proof['steps'][:-1]), ('support', proof['support'][::-1])):
            changed = deepcopy(proof)
            changed[field] = value
            self.assertFalse(verify_normal_support_ray(tri, coordinates, changed))
        for value in (-1, 100000, True, 1.0, '1'):
            changed = deepcopy(proof)
            changed['steps'][0][0] = value
            self.assertFalse(verify_normal_support_ray(tri, coordinates, changed))
        changed = deepcopy(proof)
        changed['steps'][0][1] = proof['seed']
        self.assertFalse(verify_normal_support_ray(tri, coordinates, changed))
        changed = deepcopy(proof)
        changed['steps'][0] = changed['steps'][-1]
        self.assertFalse(verify_normal_support_ray(tri, coordinates, changed))

    def test_cancellation_in_production_and_replay(self):
        tri, coordinates = layered_torus(16)
        prepared = _prepare(tri, lambda: None)
        analysed = _coordinates(prepared, coordinates, lambda: None)
        proof = peel_support_ray(prepared, analysed)
        for operation in (lambda callback: peel_support_ray(prepared, analysed, callback),
                          lambda callback: verify_support_ray(prepared, analysed, proof, callback),
                          lambda callback: verify_normal_support_ray(tri, coordinates, proof,
                                                                      check=callback)):
            for exception in (RuntimeError, ValueError, NormalOrbitError):
                counter = [0]

                def cancel():
                    counter[0] += 1
                    if counter[0] == 40:
                        raise exception('cancel ray propagation')

                with self.assertRaises(exception):
                    operation(cancel)


if __name__ == '__main__':
    unittest.main()
