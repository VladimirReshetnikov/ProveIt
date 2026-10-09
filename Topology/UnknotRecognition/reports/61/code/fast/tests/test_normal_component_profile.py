"""Source geometry, independent component oracles and proof transport."""

from copy import deepcopy
import importlib.util
import json
import random
import unittest

from fastunknot.integer_codec import json_safe
from fastunknot.normal_component_profile import (
    normal_component_profile, verify_normal_component_profile,
)
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.weighted_orbits import WeightedOrbitError
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus
from tests.test_normal_surface_orbits import relabel


class NormalComponentProfileTests(unittest.TestCase):
    def test_connected_and_disconnected_compressing_disks(self):
        raw, meridian = layered_torus(3)
        for multiple in (1, 2, 7):
            vector = [[multiple*x for x in row] for row in meridian]
            # Add a boundary-vertex link: now gcd=1 and the surface is disconnected.
            vector = [[x+int(j < 4) for j, x in enumerate(row)] for row in vector]
            result = normal_component_profile(raw, vector, record_certificate=True)
            self.assertEqual(result['components'], multiple + 1)
            self.assertEqual(result['disk_components'], multiple + 1)
            self.assertEqual(result['compressing_disk_components'], multiple)
            self.assertTrue(verify_normal_component_profile(raw, vector,
                                                           result['certificate']))
            self.assertFalse(normal_surface_topology(raw, vector)['compressing_disk'])

    def test_closed_spheres_disks_and_one_sided_components(self):
        raw, basis = interior_vertex_torus()
        for a, b, c in ((1, 2, 1), (7, 3, 2), (2, 5, 7)):
            vector = [[a*basis['sphere'][t][j]+b*basis['boundary_disk'][t][j]
                       +c*basis['mobius'][t][j] for j in range(7)] for t in range(4)]
            result = normal_component_profile(raw, vector)
            self.assertEqual(result['components'], a+b+(c+1)//2)
            self.assertEqual(result['disk_components'], b)
            self.assertEqual(result['compressing_disk_components'], 0)

    def test_huge_multiplicity_and_hexadecimal_certificate(self):
        raw, vector = layered_torus(2)
        multiple = 1 << 5000
        vector = [[multiple*x for x in row] for row in vector]
        result = normal_component_profile(raw, vector, record_certificate=True)
        self.assertEqual(result['components'], multiple)
        self.assertEqual(result['compressing_disk_components'], multiple)
        self.assertEqual(len(result['groups']), 1)
        encoded = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify_normal_component_profile(raw, vector, encoded))

    def test_empty_surface(self):
        raw, _ = layered_torus(2)
        zero = [[0]*7 for _ in range(2)]
        result = normal_component_profile(raw, zero, record_certificate=True)
        self.assertEqual((result['components'], result['disk_components'], result['groups']),
                         (0, 0, []))
        self.assertTrue(verify_normal_component_profile(raw, zero, result['certificate']))

    def test_relabelled_edge_orientations(self):
        raw, vector = layered_torus(7)
        rng = random.Random(26100943)
        for _ in range(20):
            tri, coords = relabel(raw, vector, rng)
            result = normal_component_profile(tri, coords)
            self.assertEqual(result['compressing_disk_components'], 1)

    def test_incomplete_results_have_no_profile_or_verdict(self):
        raw, vector = layered_torus(3)
        complete = normal_component_profile(raw, vector)
        for cap in (0, 1, complete['cycles']-1):
            result = normal_component_profile(raw, vector, max_cycles=cap,
                                              record_certificate=True)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            for key in ('groups', 'disk_components', 'has_compressing_disk_component',
                        'certificate'):
                self.assertNotIn(key, result)
        self.assertEqual(normal_component_profile(raw, vector,
            max_cycles=complete['cycles'])['compressing_disk_components'], 1)

    def test_tampered_profile_and_source_rejected(self):
        raw, vector = layered_torus(2)
        cert = normal_component_profile(raw, vector, record_certificate=True)['certificate']
        bad = deepcopy(cert)
        bad['profiles'][0][1][0] += 1
        self.assertFalse(verify_normal_component_profile(raw, vector, bad))
        bad = deepcopy(cert)
        bad['profiles'][0][0] = True
        self.assertFalse(verify_normal_component_profile(raw, vector, bad))
        bad = deepcopy(cert)
        bad['orbit_certificate']['orbit_count'] += 1
        self.assertFalse(verify_normal_component_profile(raw, vector, bad))
        different = [[2*x for x in row] for row in vector]
        self.assertFalse(verify_normal_component_profile(raw, different, cert))

    def test_callback_exceptions_survive_verification(self):
        raw, vector = layered_torus(1)
        cert = normal_component_profile(raw, vector, record_certificate=True)['certificate']
        for error_type in (ValueError, NormalOrbitError, WeightedOrbitError, RuntimeError):
            error = error_type('caller cancellation')
            calls = 0
            def check():
                nonlocal calls
                calls += 1
                if calls == 10:
                    raise error
            with self.assertRaises(error_type) as caught:
                verify_normal_component_profile(raw, vector, cert, check=check)
            self.assertIs(caught.exception, error)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_independent_regina_component_profiles(self):
        from collections import Counter
        from component_profile_research.oracles import fixture_corpus, regina_profiles
        for name, raw, vector in fixture_corpus(max_tetrahedra=4, trials=8):
            result = normal_component_profile(raw, vector)
            expected, counts = regina_profiles(raw, vector, result['boundary_cycle_edges'])
            actual = Counter({tuple(group[key] for key in
                ('euler_characteristic', 'normal_disks', 'boundary_vertices',
                 'cycle_0_intersections', 'cycle_1_intersections')): group['multiplicity']
                for group in result['groups']})
            self.assertEqual(actual, expected, name)
            for key, value in counts.items():
                self.assertEqual(result[key], value, (name, key))


if __name__ == '__main__':
    unittest.main()
