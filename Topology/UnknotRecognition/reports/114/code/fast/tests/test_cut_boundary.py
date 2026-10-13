"""Whole cut-boundary cells, source replay and actual 3D cutting oracles."""
from collections import Counter
from contextlib import ExitStack
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_boundary import normal_cut_boundary
from fastunknot.normal_cut_boundary_verify import verify_normal_cut_boundary
from fastunknot.normal_surface_geometry import NormalOrbitError
from normal_orbit_research.cut_boundary import literal_complex, native_profiles, regina_profiles
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel

ROOT = Path(__file__).resolve().parents[2]
REGINA = importlib.util.find_spec('regina') is not None


class CutBoundaryTests(unittest.TestCase):
    def test_empty_cut_meridians_vertex_links_and_one_sided_multiples(self):
        raw, meridian = layered_torus(1)
        for kind, vector in (('meridian', meridian), ('link', [[1, 1, 1, 1, 0, 0, 0]]),
                             ('mobius', [[0, 0, 0, 0, 0, 1, 0]])):
            for copies in (0, 1, 2, 3, 7, 16):
                rows = [[copies*x for x in row] for row in vector]
                result = normal_cut_boundary(raw, rows, record_certificate=True)
                self.assertTrue(verify_normal_cut_boundary(raw, rows, result['certificate']))
                boundary, pieces = native_profiles(result['summary'])
                if not copies:
                    expected = Counter({1: 1}); expected_pieces = Counter({(1, 1): 1})
                elif kind == 'meridian':
                    expected = Counter({0: copies}); expected_pieces = Counter({(1, 0): copies})
                elif kind == 'link':
                    expected = Counter({0: copies, 1: 1}); expected_pieces = Counter({(1, 0): copies, (1, 1): 1})
                else:
                    expected = Counter({1: copies//2+1}); expected_pieces = Counter({(1, 1): copies//2+1})
                self.assertEqual(boundary, expected); self.assertEqual(pieces, expected_pieces)

    def test_oriented_cell_boundaries_vertex_links_and_weighted_inventory(self):
        for t in (1, 2, 4, 8):
            raw, base = layered_torus(t)
            for copies in (0, 1, 2, 5):
                result = normal_cut_boundary(raw, [[copies*x for x in row] for row in base])
                literal = literal_complex(raw, result['geometry'])
                expected = Counter()
                for row in result['summary']['boundary_profiles']:
                    expected[row['euler_characteristic'], row['horizontal_polygons'], row['original_polygons']] += row['multiplicity']
                self.assertEqual(literal['boundary_histogram'], expected)
                self.assertEqual(literal['oriented_edge_incidences'], 2*result['geometry']['edge_points'])
                self.assertEqual(literal['connected_vertex_links'], result['geometry']['vertex_points'])

    def test_source_relabellings_preserve_topology_and_oriented_cycles(self):
        rng = random.Random(26101121)
        for t in (1, 2, 4):
            raw, vector = layered_torus(t)
            vector = [[3*x for x in row] for row in vector]
            expected = native_profiles(normal_cut_boundary(raw, vector)['summary'])
            for _ in range(12):
                changed, rows = relabel(raw, vector, rng)
                result = normal_cut_boundary(changed, rows, record_certificate=True)
                self.assertEqual(native_profiles(result['summary']), expected)
                self.assertTrue(verify_normal_cut_boundary(changed, rows, result['certificate']))
                literal_complex(changed, result['geometry'])

    def test_multiple_boundary_components_owned_by_a_single_cut_piece(self):
        records = json.loads((ROOT/'synthesis/data/cut-complement-audit.json').read_text())['source_proofs']
        case = next(r for r in records if r['id'] == 'solid_torus_sum_s2xs1/0')
        result = normal_cut_boundary(case['triangulation'], case['coordinates'], record_certificate=True)
        self.assertEqual(native_profiles(result['summary'])[1], Counter({(2, 1): 1}))
        self.assertTrue(verify_normal_cut_boundary(case['triangulation'], case['coordinates'], result['certificate']))
        literal_complex(case['triangulation'], result['geometry'])

    def test_binary_cells_and_multiplicities_without_expansion(self):
        raw, base = layered_torus(1); copies = 1 << 16384
        rows = [[copies*x for x in row] for row in base]
        result = normal_cut_boundary(raw, rows, record_certificate=True)
        self.assertEqual(native_profiles(result['summary']), (Counter({0: copies}), Counter({(1, 0): copies})))
        self.assertLessEqual(len(result['geometry']['faces']), 30)
        self.assertLessEqual(len(result['geometry']['edges']), 126)
        self.assertLessEqual(len(result['geometry']['carriers']), 46)
        wire = json.loads(json.dumps(json_safe(result['certificate'])))
        disabled = ('fastunknot.normal_cut_boundary._boundary_system', 'fastunknot.normal_cut_boundary._cycle_recipes',
                    'fastunknot.normal_cut_boundary._boundary_summary', 'fastunknot.normal_cut_boundary._piece_summary',
                    'fastunknot.normal_cut_boundary.normal_cut_boundary', 'fastunknot.normal_cut_complement._chamber_system',
                    'fastunknot.orbit_transversal.orbit_transversal', 'fastunknot.orbit_transversal._forward_selector',
                    'fastunknot.weighted_orbits.weighted_orbit_histogram',
                    'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate',
                    'fastunknot.interval_orbits.count_orbits')
        with ExitStack() as stack:
            for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_boundary(raw, json_safe(rows), wire))

    def test_changed_geometry_cyclic_attachments_ownership_and_summaries_rejected(self):
        raw, rows = layered_torus(4)
        proof = normal_cut_boundary(raw, rows, record_certificate=True)['certificate']; mutations = []
        for key, value in (('schema', 'normal-cut-components-v1'), ('input_sha256', '0'*64), ('pieces', None)):
            bad = deepcopy(proof); bad[key] = value; mutations.append(bad)
        for key in ('face_points', 'edge_points', 'vertex_points', 'chamber_points'):
            bad = deepcopy(proof); bad['geometry'][key] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['edges'][0]['ends'][0][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['faces'][0]['cycle'][0]['forward'] ^= True; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['carriers'][0]['chamber_start'] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['summary']['piece_profiles'][0]['total_boundary_genus'] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['summary']['cut_components'] = True; mutations.append(bad)
        bad = deepcopy(proof); bad['boundary_transversal']['representative_intervals'][0][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['boundary_weights']['histogram'][0]['weight'][0] += 2; mutations.append(bad)
        bad = deepcopy(proof); bad['pieces']['histogram'][0]['weight'][1] += 1; mutations.append(bad)
        for bad in mutations: self.assertFalse(verify_normal_cut_boundary(raw, rows, bad))
        self.assertFalse(verify_normal_cut_boundary(raw, [[2*x for x in row] for row in rows], proof))

    def test_shared_discovery_cap_and_replay_operation_limit(self):
        raw, rows = layered_torus(2); full = normal_cut_boundary(raw, rows, record_certificate=True)
        cycles = full['stats']['boundary']['orbit_cycles']+full['stats']['pieces']['orbit_cycles']
        for allowance in (0, cycles-1):
            result = normal_cut_boundary(raw, rows, max_cycles=allowance, record_certificate=True)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            for field in ('geometry', 'summary', 'certificate'): self.assertNotIn(field, result)
        self.assertEqual(normal_cut_boundary(raw, rows, max_cycles=cycles)['summary'], full['summary'])
        self.assertFalse(verify_normal_cut_boundary(raw, rows, full['certificate'], max_operations=0))
        operations = sum(len(full['certificate'][key]['orbit_proof']['operations'])
                         for key in ('boundary_transversal', 'boundary_weights', 'pieces'))
        self.assertTrue(verify_normal_cut_boundary(raw, rows, full['certificate'], max_operations=operations))

    def test_invalid_sources_arguments_and_external_cancellation(self):
        raw, rows = layered_torus(1)
        with self.assertRaises(ValueError): normal_cut_boundary(raw, rows, max_cycles=True)
        with self.assertRaises(ValueError): normal_cut_boundary(raw, rows, record_certificate=1)
        with self.assertRaises(NormalOrbitError): normal_cut_boundary(raw, [[-1]*7])
        class Stop(Exception): pass
        class Cancel:
            def __bool__(self): return False
            def __call__(self): raise Stop()
        with self.assertRaises(Stop): normal_cut_boundary(raw, rows, check=Cancel())
        proof = normal_cut_boundary(raw, rows, record_certificate=True)['certificate']
        with self.assertRaises(Stop): verify_normal_cut_boundary(raw, rows, proof, check=Cancel())
        with self.assertRaises(ValueError): verify_normal_cut_boundary(raw, rows, proof, max_operations=True)

    @unittest.skipUnless(REGINA, 'Regina supplies the independent explicit cutting oracle')
    def test_saved_source_profiles_match_actual_three_dimensional_cuts(self):
        cases = json.loads((ROOT/'synthesis/data/cut-complement-audit.json').read_text())['source_proofs']
        for c in cases:
            rows = c['coordinates']
            if any(isinstance(x, str) for row in rows for x in row) or sum(map(sum, rows)) > 256: continue
            answer = normal_cut_boundary(c['triangulation'], rows, record_certificate=True)
            expected_boundary, expected_pieces, _ = regina_profiles(c['triangulation'], rows)
            self.assertEqual(native_profiles(answer['summary']), (expected_boundary, expected_pieces), c['id'])
            self.assertTrue(verify_normal_cut_boundary(c['triangulation'], rows, answer['certificate']))

    @unittest.skipUnless(REGINA, 'Regina supplies the independent interior topology oracle')
    def test_sphere_boundary_does_not_certify_a_ball(self):
        from normal_orbit_research.fixtures import regina_triangulation, regina_surface
        case = next(r for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']
                    if r['id'] == 'solid_torus_sum_rp3')
        rows = case['standard_vertices'][6]['coordinates']
        answer = normal_cut_boundary(case['triangulation'], rows, record_certificate=True)
        self.assertEqual(native_profiles(answer['summary'])[1], Counter({(1, 0): 1}))
        cut = regina_surface(regina_triangulation(case['triangulation']), rows).cutAlong()
        self.assertFalse(cut.isBall()); self.assertEqual(cut.homology().str(), 'Z_2')
        self.assertNotIn('ball', answer['summary']); self.assertNotIn('unknot', answer)


if __name__ == '__main__': unittest.main()
