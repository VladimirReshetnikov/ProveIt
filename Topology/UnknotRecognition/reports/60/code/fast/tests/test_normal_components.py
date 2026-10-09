"""Independent geometry checks for connected-component coordinate extraction."""
from copy import deepcopy
from collections import Counter
import importlib.util
import random
import unittest

from fastunknot.normal_components import (
    normal_component_inventory, verify_normal_component_certificate,
)
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.integer_codec import json_safe
from normal_orbit_research.fixtures import (
    layered_torus, interior_vertex_torus, boundary_cap,
    regina_triangulation, regina_surface, export_surface,
)
from test_normal_surface_orbits import relabel


def vector(rows):
    return tuple(x for row in rows for x in row)


def profiles(answer):
    return {vector(p['coordinates']): p['multiplicity'] for p in answer['profiles']}


class NormalComponentInventoryTests(unittest.TestCase):
    def test_disconnected_meridians_are_extracted(self):
        for t in (1, 3, 8, 16):
            tri, meridian = layered_torus(t)
            for scale in (1, 7, 2 ** 1024):
                coords = [[scale * x for x in row] for row in meridian]
                result = normal_component_inventory(tri, coords, record_certificate=True)
                self.assertEqual(profiles(result), {vector(meridian): scale})
                self.assertEqual(result['compressing_disk_components'], scale)
                self.assertTrue(verify_normal_component_certificate(tri, coords,
                                                                   result['certificate']))
                if scale != 1:
                    self.assertFalse(normal_surface_topology(tri, coords)['compressing_disk'])

    def test_one_sided_surface_and_double_are_distinct_profiles(self):
        tri, _ = layered_torus(1)
        unit = [[0, 0, 0, 0, 0, 1, 0]]
        doubled = [[0, 0, 0, 0, 0, 2, 0]]
        for scale in (1, 2, 3, 8, 2 ** 2048 + 1):
            coords = [[scale * x for x in unit[0]]]
            result = normal_component_inventory(tri, coords, record_certificate=True)
            expected = {}
            if scale % 2:
                expected[vector(unit)] = 1
            if scale // 2:
                expected[vector(doubled)] = scale // 2
            self.assertEqual(profiles(result), expected)
            self.assertFalse(result['has_compressing_disk'])
            self.assertTrue(verify_normal_component_certificate(tri, coords,
                                                               json_safe(result['certificate'])))

    def test_primitive_total_with_huge_mixed_multiplicities(self):
        tri, meridian = layered_torus(3)
        link = [[1, 1, 1, 1, 0, 0, 0] for _ in meridian]
        k, ell = 2 ** 1000, 2 ** 1000 + 1
        coords = [[k * x + ell * y for x, y in zip(a, b)]
                  for a, b in zip(meridian, link)]
        result = normal_component_inventory(tri, coords, record_certificate=True)
        self.assertEqual(profiles(result), {vector(meridian): k, vector(link): ell})
        self.assertEqual(result['compressing_disk_components'], k)
        self.assertTrue(verify_normal_component_certificate(tri, coords, result['certificate']))

    def test_empty_surface_and_resource_caps(self):
        tri, meridian = layered_torus(3)
        zero = [[0] * 7 for _ in meridian]
        result = normal_component_inventory(tri, zero, record_certificate=True)
        self.assertEqual(result['profiles'], [])
        self.assertEqual(result['components'], 0)
        self.assertFalse(result['has_compressing_disk'])
        self.assertTrue(verify_normal_component_certificate(tri, zero, result['certificate']))
        for cap in ({'max_cycles': 0}, {'max_operations': 0},
                    {'max_weight_blocks': 0}, {'max_output_records': 0}):
            answer = normal_component_inventory(tri, meridian, **cap, record_certificate=True)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('profiles', answer)
            self.assertNotIn('certificate', answer)

    def test_forged_inventory_and_source_are_rejected(self):
        tri, meridian = layered_torus(2)
        coords = [[3 * x for x in row] for row in meridian]
        proof = normal_component_inventory(tri, coords, record_certificate=True)['certificate']
        bads = []
        for key, value in [('multiplicity', 4), ('euler_characteristic', 0),
                           ('disk', False), ('compressing_disk', False),
                           ('normal_disks', True)]:
            bad = deepcopy(proof)
            bad['profiles'][0][key] = value
            bads.append(bad)
        bad = deepcopy(proof)
        bad['profiles'][0]['coordinates'][0][0] += 1
        bads.append(bad)
        bad = deepcopy(proof)
        bad['weighted']['classes'][0][1] += 1
        bads.append(bad)
        bad = deepcopy(proof)
        bad['boundary_homology'][0] = {'nonzero': False, 'vertex_values': []}
        bads.append(bad)
        for bad in bads:
            self.assertFalse(verify_normal_component_certificate(tri, coords, bad))
        foreign = [[4 * x for x in row] for row in meridian]
        self.assertFalse(verify_normal_component_certificate(tri, foreign, proof))

    def test_cancellation_is_not_a_negative_claim(self):
        tri, coords = layered_torus(2)
        proof = normal_component_inventory(tri, coords, record_certificate=True)['certificate']
        class Cancel(ValueError):
            pass
        for function in (lambda check: normal_component_inventory(tri, coords, check=check),
                         lambda check: verify_normal_component_certificate(
                             tri, coords, proof, check=check)):
            for stop in (1, 30, 100, 250):
                count = [0]
                def check():
                    count[0] += 1
                    if count[0] == stop:
                        raise Cancel('test cancellation')
                with self.assertRaises(Cancel):
                    function(check)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle')
    def test_regina_components_and_relabelled_anchors(self):
        rng = random.Random(261009101)
        cases = []
        for count in (1, 2, 4):
            tri, meridian = layered_torus(count)
            cases.append((tri, meridian))
            cases.append(boundary_cap(tri, meridian))
        tri, basis = interior_vertex_torus()
        for _ in range(18):
            coeff = [rng.randrange(4) for _ in range(3)]
            coords = [[sum(coeff[j] * basis[name][t][kind]
                           for j, name in enumerate(('sphere', 'boundary_disk', 'mobius')))
                       for kind in range(7)] for t in range(4)]
            cases.append((tri, coords))
        checks = 0
        for tri, coords in cases:
            for _ in range(3):
                raw, changed = relabel(tri, coords, rng)
                rt = regina_triangulation(raw)
                surface = regina_surface(rt, changed)
                oracle = Counter(vector(export_surface(component)) for component in surface.components())
                result = normal_component_inventory(raw, changed, record_certificate=True)
                self.assertEqual(profiles(result), dict(oracle))
                self.assertTrue(verify_normal_component_certificate(raw, changed,
                                                                   result['certificate']))
                checks += 1
        self.assertEqual(checks, 72)

