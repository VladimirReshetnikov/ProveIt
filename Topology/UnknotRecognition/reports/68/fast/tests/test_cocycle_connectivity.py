"""Topological hypotheses, gauge invariance, forgeries and independent replay."""
from copy import deepcopy
from contextlib import ExitStack
import json
from math import gcd
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, local_coordinates
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate, _primitive_cochain
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.integer_codec import json_safe


def certificate(diagram, raw, heights, coordinates, span=None):
    return dict(schema='diagram-cocycle-disc-v1', input_pd=[list(row) for row in diagram.pd],
                triangulation=raw, heights=heights, coordinates=coordinates, span_certificate=span)


class CocycleConnectivityTests(unittest.TestCase):
    def test_replay_and_recognition_without_orbit_or_discovery_engines(self):
        for diagram in (Diagram.from_pd([]), Diagram.from_braid(4, [-1, 2, 1, -2, 3])):
            with patch('fastunknot.normal_surface_components.normal_component_census', side_effect=AssertionError), \
                 patch('fastunknot.interval_orbits.count_orbits', side_effect=AssertionError):
                result = normal_seed_decide(diagram, max_cycles=0)
            self.assertEqual(result['status'], 'UNKNOT')
            proof = json.loads(json.dumps(result['certificate']))
            with ExitStack() as stack:
                for target in ('normal_seed.normal_seed_decide', 'normal_cocycle.rank_one_cocycle_seed',
                               'cocycle_span.minimize_cocycle_span', 'diagram_exterior.diagram_exterior',
                               'normal_disk_kernel.normal_compressing_disk_count',
                               'normal_surface_components.normal_component_census', 'interval_orbits.count_orbits',
                               'interval_orbit_verify.verify_orbit_certificate'):
                    stack.enter_context(patch('fastunknot.'+target, side_effect=AssertionError))
                self.assertTrue(verify_normal_seed_certificate(diagram, proof))
            summary = inspect_cocycle_certificate(diagram, proof)
            self.assertEqual(summary['components'], 1)
            self.assertEqual(summary['euler_characteristic'], 1)

    def test_primitive_chi_one_without_connectivity_is_not_a_disc(self):
        # A genuine trefoil surface: primitive, chi=1, but three components
        # and no essential disc. Vertex-potential changes can add zero classes.
        diagram = Diagram.from_braid(2, [1, 1, 1])
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        heights = [[x-2*int(v == 3) for x, v in zip(hs, vs)]
                   for hs, vs in zip(seed['heights'], seed['vertices'])]
        coordinates = [local_coordinates(row) for row in heights]
        prepared = _prepare(raw, lambda: None)
        self.assertIsNotNone(_primitive_cochain(prepared, heights, False, lambda: None))
        self.assertIsNone(_primitive_cochain(prepared, heights, True, lambda: None))
        self.assertEqual(_coordinates(prepared, coordinates, lambda: None)['euler_characteristic'], 1)
        control = normal_component_census(raw, coordinates)
        self.assertEqual(control['components'], 3)
        self.assertEqual(control['compressing_disk_components'], 0)
        proof = certificate(diagram, raw, heights, coordinates)
        self.assertFalse(verify_normal_seed_certificate(diagram, proof))
        optimum = minimize_cocycle_span(seed['vertices'], heights)['certificate']
        # Even a genuine minimum witness cannot authenticate different coords.
        proof['span_certificate'] = optimum
        self.assertFalse(verify_normal_seed_certificate(diagram, proof))
        optimum['coordinates'] = coordinates
        optimum['disc_count'] = sum(map(sum, coordinates))
        optimum['potential'] = [0]*len(optimum['vertex_ids'])
        self.assertFalse(verify_normal_seed_certificate(diagram, proof))

    def test_primitivity_requires_tree_gauge_not_raw_coordinate_gcd(self):
        diagram = Diagram.from_pd([])
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        prepared = _prepare(raw, lambda: None)
        # Double the class and add a unit vertex coboundary: raw edge gcd=1.
        vertex = min(prepared['vertex_roots'])
        for multiplier in (0, 2):
            heights = [[multiplier*x+int(v == vertex) for x, v in zip(hs, vs)]
                       for hs, vs in zip(seed['heights'], seed['vertices'])]
            differences = [hs[b]-hs[a] for hs in heights for a in range(4) for b in range(a+1, 4)]
            self.assertEqual(gcd(*differences), 1)
            self.assertIsNone(_primitive_cochain(prepared, heights, False, lambda: None))
            optimum = minimize_cocycle_span(seed['vertices'], heights)
            proof = certificate(diagram, raw, heights, optimum['coordinates'], optimum['certificate'])
            self.assertIsNone(inspect_cocycle_certificate(diagram, proof))

    def test_large_gauge_and_tetrahedron_offsets_preserve_checked_class(self):
        for diagram in (Diagram.from_pd([]), Diagram.from_braid(4, [-1, 2, 1, -2, 3])):
            proof = normal_seed_decide(diagram)['certificate']
            prepared = _prepare(proof['triangulation'], lambda: None)
            span = proof['span_certificate']
            potential = {v: (v+1)*(1 << 20000) for v in prepared['vertex_roots']}
            for t, row in enumerate(proof['heights']):
                for i in range(4):
                    row[i] += (t+1)*(1 << 20001)
                    if span is not None:
                        row[i] += potential[prepared['vertex_roots'][4*t+i]]
            if span is not None:
                span['potential'] = [x-potential[v] for v, x in zip(span['vertex_ids'], span['potential'])]
            transported = json.loads(json.dumps(json_safe(proof)))
            self.assertTrue(verify_normal_seed_certificate(diagram, transported))

    def test_mutations_and_legacy_certificate_compatibility(self):
        diagram = Diagram.from_braid(4, [-1, 2, 1, -2, 3])
        proof = normal_seed_decide(diagram)['certificate']
        for key in proof:
            bad = deepcopy(proof); del bad[key]
            self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        for field, value in (('heights', []), ('heights', True), ('span_certificate', None),
                             ('span_certificate', {}), ('coordinates', []), ('input_pd', [])):
            self.assertFalse(verify_normal_seed_certificate(diagram, dict(proof, **{field: value})))
        for value in (True, 0.5, '1', None):
            bad = deepcopy(proof); bad['heights'][0][0] = value
            self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        bad = deepcopy(proof); bad['heights'][0][0] += 1
        self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        for field in ('potential', 'matching', 'coordinates', 'disc_count', 'vertex_ids', 'schema'):
            bad = deepcopy(proof); bad['span_certificate'][field] = False
            self.assertFalse(verify_normal_seed_certificate(diagram, bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2, [1, 1, 1]), proof))

    def test_cancellation_reaches_all_replay_phases(self):
        diagram = Diagram.from_braid(4, [-1, 2, 1, -2, 3])
        proof = normal_seed_decide(diagram)['certificate']
        calls = [0]
        def count(): calls[0] += 1
        self.assertTrue(verify_normal_seed_certificate(diagram, proof, check=count))
        total = calls[0]
        for stop in (1, total//2, total):
            calls[0] = 0
            def cancel():
                count()
                if calls[0] == stop: raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError, 'cancelled'):
                verify_normal_seed_certificate(diagram, proof, check=cancel)


if __name__ == '__main__':
    unittest.main()
