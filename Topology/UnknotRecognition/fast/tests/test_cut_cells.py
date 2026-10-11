"""Full interior cut cells, integral chains and independently checked sources."""
from contextlib import ExitStack
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_cells import normal_cut_cell_complex
from fastunknot.normal_cut_cells_verify import verify_normal_cut_cell_complex
from fastunknot.normal_surface_geometry import NormalOrbitError
from normal_orbit_research.cut_cells import literal_chains, regina_cut_homology
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel

ROOT = Path(__file__).resolve().parents[2]
REGINA = importlib.util.find_spec('regina') is not None


class CutCellTests(unittest.TestCase):
    def test_complete_cells_and_integral_chain_compositions(self):
        for t in (1, 2, 4, 8):
            raw, base = layered_torus(t)
            for n in (0, 1, 2, 5):
                rows = [[n*x for x in row] for row in base]
                result = normal_cut_cell_complex(raw, rows, record_certificate=True)
                self.assertTrue(verify_normal_cut_cell_complex(raw, rows, result['certificate']))
                # Keep the wide finite case's integral chain and link checks;
                # binary Gaussian rank avoids cubic sparse-field work there.
                primes = (2,) if t == 8 and n > 1 else (2, 3)
                literal = literal_chains(raw, result['geometry'], max_cells=20000, primes=primes)
                expected = [1, 1, 0, 0] if n == 0 else [n, 0, 0, 0]
                self.assertEqual(literal['betti'], {p: expected for p in primes})
                self.assertEqual(result['summary']['euler_characteristic'], n)
                self.assertEqual(literal['chain_zero_checks'], result['geometry']['face_points']+result['geometry']['chamber_points'])

    def test_one_sided_cut_chains_and_unscaled_multiplicity(self):
        raw, _ = layered_torus(1)
        for n in range(1, 12):
            rows = [[0, 0, 0, 0, 0, n, 0]]
            result = normal_cut_cell_complex(raw, rows, record_certificate=True)
            self.assertTrue(verify_normal_cut_cell_complex(raw, rows, result['certificate']))
            literal = literal_chains(raw, result['geometry'])
            self.assertEqual(literal['betti'][2][0], n//2+1)
            self.assertEqual(literal['betti'][3][0], n//2+1)
            self.assertEqual(result['geometry']['chamber_points'], n+1)

    def test_relabellings_preserve_homology_and_source_chamber_maps(self):
        rng = random.Random(26101131)
        for t in (1, 2, 4):
            raw, rows = layered_torus(t); rows = [[3*x for x in row] for row in rows]
            for _ in range(12):
                changed, vector = relabel(raw, rows, rng)
                result = normal_cut_cell_complex(changed, vector, record_certificate=True)
                self.assertTrue(verify_normal_cut_cell_complex(changed, vector, result['certificate']))
                self.assertEqual(literal_chains(changed, result['geometry'])['betti'], {2: [3, 0, 0, 0], 3: [3, 0, 0, 0]})

    def test_interior_vertices_and_faces_survive_the_raw_cut(self):
        bank = json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']
        source = next(r for r in bank if r['id'] == 'interior_1_2')['triangulation']
        result = normal_cut_cell_complex(source, [[0]*7 for _ in source['tetrahedra']], record_certificate=True)
        self.assertTrue(any(not v['boundary'] for v in result['geometry']['vertices']))
        self.assertTrue(any(not f['boundary'] for f in result['geometry']['faces']))
        self.assertTrue(verify_normal_cut_cell_complex(source, [[0]*7 for _ in source['tetrahedra']], result['certificate']))
        literal_chains(source, result['geometry'])

    def test_large_binary_geometry_and_producer_disabled_source_replay(self):
        raw, base = layered_torus(1); n = 1 << 16384; rows = [[n*x for x in row] for row in base]
        disabled = ('fastunknot.normal_cut_cells._cut_cells', 'fastunknot.normal_cut_cells._orientations',
                    'fastunknot.normal_cut_cells._summary', 'fastunknot.normal_cut_cells.normal_cut_cell_complex',
                    'fastunknot.normal_cut_boundary._cycle_recipes', 'fastunknot.normal_cut_boundary._boundary_system',
                    'fastunknot.normal_cut_complement._chamber_system', 'fastunknot.interval_orbits.count_orbits')
        with patch('fastunknot.interval_orbits.count_orbits', side_effect=AssertionError('discovery')):
            result = normal_cut_cell_complex(raw, rows, record_certificate=True)
        self.assertEqual(result['summary']['euler_characteristic'], n)
        self.assertEqual(len(result['geometry']['chambers']), 3)
        self.assertEqual(len(result['geometry']['edges']), 15)
        wire = json.loads(json.dumps(json_safe(result['certificate'])))
        with ExitStack() as stack:
            for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_cell_complex(raw, json_safe(rows), wire))
        with self.assertRaises(ValueError): literal_chains(raw, result['geometry'])

    def test_forged_interior_cells_incidence_and_boundary_flags_rejected(self):
        raw, rows = layered_torus(4); proof = normal_cut_cell_complex(raw, rows, record_certificate=True)['certificate']
        mutations = []
        for key, value in (('schema', 'normal-cut-boundary-v1'), ('input_sha256', '0'*64), ('summary', None)):
            bad = deepcopy(proof); bad[key] = value; mutations.append(bad)
        for key in ('vertex_points', 'edge_points', 'face_points', 'chamber_points'):
            bad = deepcopy(proof); bad['geometry'][key] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['faces'][0]['boundary'] = False; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['faces'][0]['cycle'][0]['forward'] ^= True; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['face_incidence'][0]['sign'] *= -1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['face_incidence'][0]['chamber'][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['edges'][0]['incidences'][0]['face'][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['edges'][-1]['endpoint_pieces'][0]['ends'][0][1] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['summary']['euler_characteristic'] = True; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['coordinates'][0][0] += 1; mutations.append(bad)
        bad = deepcopy(proof); bad['geometry']['source']['tetrahedra'][0][0]['permutation'].reverse(); mutations.append(bad)
        for bad in mutations: self.assertFalse(verify_normal_cut_cell_complex(raw, rows, bad))
        self.assertFalse(verify_normal_cut_cell_complex(raw, [[2*x for x in row] for row in rows], proof))

    def test_reconstruction_packet_does_not_alias_mutable_source(self):
        raw, rows = layered_torus(2); result = normal_cut_cell_complex(raw, rows)
        expected_source, expected_rows = deepcopy(raw), deepcopy(rows)
        raw['tetrahedra'][0][0]['permutation'].reverse(); rows[0][0] += 1
        self.assertEqual(result['geometry']['source'], expected_source)
        self.assertEqual(result['geometry']['coordinates'], expected_rows)

    def test_invalid_source_and_false_valued_cancellation(self):
        raw, rows = layered_torus(1)
        with self.assertRaises(ValueError): normal_cut_cell_complex(raw, rows, record_certificate=1)
        with self.assertRaises(NormalOrbitError): normal_cut_cell_complex(raw, [[-1]*7])
        class Stop(Exception): pass
        class Cancel:
            def __bool__(self): return False
            def __call__(self): raise Stop()
        with self.assertRaises(Stop): normal_cut_cell_complex(raw, rows, check=Cancel())
        proof = normal_cut_cell_complex(raw, rows, record_certificate=True)['certificate']
        with self.assertRaises(Stop): verify_normal_cut_cell_complex(raw, rows, proof, check=Cancel())

    @unittest.skipUnless(REGINA, 'Regina supplies independent full cut homology')
    def test_saved_source_chains_match_regina_over_two_prime_fields(self):
        cases = json.loads((ROOT/'synthesis/data/cut-complement-audit.json').read_text())['source_proofs']
        for c in cases:
            rows = c['coordinates']
            if any(isinstance(x, str) for row in rows for x in row) or sum(map(sum, rows)) > 256: continue
            result = normal_cut_cell_complex(c['triangulation'], rows, record_certificate=True)
            self.assertTrue(verify_normal_cut_cell_complex(c['triangulation'], rows, result['certificate']), c['id'])
            literal = literal_chains(c['triangulation'], result['geometry'])
            betti, genera, _, chi = regina_cut_homology(c['triangulation'], rows)
            self.assertEqual(literal['betti'], betti, c['id']); self.assertEqual(literal['boundary_genera'], genera, c['id'])
            self.assertEqual(result['summary']['euler_characteristic'], chi, c['id'])

    @unittest.skipUnless(REGINA, 'Regina supplies the sphere-boundary nonball oracle')
    def test_interior_torsion_is_present_despite_sphere_boundary(self):
        case = next(r for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records'] if r['id'] == 'solid_torus_sum_rp3')
        rows = case['standard_vertices'][6]['coordinates']; result = normal_cut_cell_complex(case['triangulation'], rows, record_certificate=True)
        literal = literal_chains(case['triangulation'], result['geometry'])
        self.assertEqual(literal['betti'], {2: [1, 1, 1, 0], 3: [1, 0, 0, 0]})
        self.assertTrue(verify_normal_cut_cell_complex(case['triangulation'], rows, result['certificate']))
        self.assertNotIn('ball', result['summary']); self.assertNotIn('unknot', result)


if __name__ == '__main__': unittest.main()
