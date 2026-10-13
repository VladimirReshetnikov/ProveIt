"""Compact coordinates preserve full inventories and independent source replay."""
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus, boundary_cap
from test_normal_components import combination, relabel


class CoordinateBasisTests(unittest.TestCase):
    def test_legacy_certificate_replay_and_version_separation(self):
        case = json.loads((Path(__file__).parent/'fixtures/normal_component_v1.json').read_text())
        raw, vector, proof = (case[k] for k in ('triangulation', 'coordinates', 'certificate'))
        self.assertTrue(verify_normal_component_certificate(raw, vector, proof))
        answer = normal_component_census(raw, vector, mode='coordinates', record_certificate=True)
        self.assertEqual(answer['component_histogram'], proof['summary']['component_histogram'])
        for certificate, schema in ((proof, 'normal-component-census-v2'),
                                    (answer['certificate'], 'normal-component-census-v1')):
            bad = deepcopy(certificate)
            bad['schema'] = schema
            self.assertFalse(verify_normal_component_certificate(raw, vector, bad))

    def test_vertex_anchors_one_sided_types_and_large_binary_multiplicities(self):
        raw, _ = layered_torus(1)
        factor = 2**5000+1
        for scale, expected in ((3, {(1,1,1,1,0,0,0): factor,
                                     (0,0,0,0,0,1,0): 1, (0,0,0,0,0,2,0): 1}),
                                (2*factor, {(1,1,1,1,0,0,0): factor,
                                            (0,0,0,0,0,2,0): factor})):
            vector = [[factor]*4+[0, scale, 0]]
            answer = normal_component_census(raw, vector, mode='coordinates', record_certificate=True)
            self.assertEqual(answer['weight_dimension'], 2)
            actual = {tuple(row['coordinates'][0]): row['multiplicity']
                      for row in answer['component_histogram']}
            self.assertEqual(actual, expected)
            proof = json.loads(json.dumps(json_safe(answer['certificate'])))
            self.assertTrue(verify_normal_component_certificate(raw, vector, proof))

    def test_multiple_vertices_zero_anchors_and_relabeling(self):
        raw, basis = interior_vertex_torus()
        rng = random.Random(261009441)
        for coefficients in ((0,0,0), (3,5,0), (0,0,3), (3,5,3)):
            vector = combination(list(basis.values()), coefficients)
            expected = normal_component_census(raw, vector, mode='summary')
            for _ in range(5):
                changed, coords = relabel(raw, vector, rng)
                answer = normal_component_census(changed, coords, mode='coordinates', record_certificate=True)
                self.assertEqual(answer['components'], expected['components'])
                self.assertTrue(verify_normal_component_certificate(changed, coords, answer['certificate']))
                reconstructed = [[0]*7 for _ in coords]
                for row in answer['component_histogram']:
                    for t, entries in enumerate(row['coordinates']):
                        for j, value in enumerate(entries):
                            reconstructed[t][j] += row['multiplicity']*value
                self.assertEqual(reconstructed, coords)

    def test_checker_independence_mutation_and_cancellation(self):
        raw, vector = boundary_cap(*layered_torus(5))
        proof = normal_component_census(raw, vector, mode='coordinates', record_certificate=True)['certificate']
        with patch('fastunknot.normal_surface_components.coordinate_basis', side_effect=AssertionError), \
             patch('fastunknot.normal_surface_components.coordinate_decoder', side_effect=AssertionError), \
             patch('fastunknot.weighted_orbits._replay', side_effect=AssertionError):
            self.assertTrue(verify_normal_component_certificate(raw, vector, proof))
        bad = deepcopy(proof)
        bad['summary']['component_histogram'][0]['coordinates'][0][0] += 1
        self.assertFalse(verify_normal_component_certificate(raw, vector, bad))
        bad = deepcopy(proof)
        bad['weighted_orbits']['histogram'][0]['weight'][0] += 1
        self.assertFalse(verify_normal_component_certificate(raw, vector, bad))
        class Cancelled(Exception):
            pass
        for operation in (lambda cb: normal_component_census(raw, vector, mode='coordinates', check=cb),
                          lambda cb: verify_normal_component_certificate(raw, vector, proof, check=cb)):
            def count():
                nonlocal calls
                calls += 1
            calls = 0
            operation(count)
            limit = calls-1
            def cancel():
                nonlocal calls
                calls += 1
                if calls == limit:
                    raise Cancelled()
            calls = 0
            with self.assertRaises(Cancelled):
                operation(cancel)
