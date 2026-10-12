"""Source-authenticated relative top cancellations and hostile composition."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.core_top_reduction import reduce_core_top_handles, source_core_top_incidence
from fastunknot.core_top_reduction_verify import replay_core_top_reduction
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from normal_orbit_research.fixtures import interior_vertex_torus, layered_torus


def _interior_loop_torus():
    """A real source: one 1-4 move followed by one 2-3 move on a solid torus.

    Its five-tetrahedron isomorphism signature is fLHPccdedehspga. The interior
    edge with representative 14 has two different ends at the same vertex.
    This saved face pairing keeps the multiplicity test independent of Regina.
    """
    specifications = [
        [(4, [1, 2, 3, 0]), (2, [1, 0, 2, 3]), (1, [0, 1, 3, 2]), None],
        [(2, [3, 2, 0, 1]), (3, [1, 0, 2, 3]), None, (0, [0, 1, 3, 2])],
        [(0, [1, 0, 2, 3]), (4, [0, 3, 2, 1]), (3, [0, 1, 3, 2]), (1, [2, 3, 1, 0])],
        [(1, [1, 0, 2, 3]), (4, [0, 2, 1, 3]), (4, [1, 3, 0, 2]), (2, [0, 1, 3, 2])],
        [(3, [2, 0, 3, 1]), (0, [3, 0, 1, 2]), (3, [0, 2, 1, 3]), (2, [0, 3, 2, 1])],
    ]
    return {'tetrahedra': [[None if item is None else
            dict(tetrahedron=item[0], permutation=item[1]) for item in row]
            for row in specifications]}


class CoreTopReductionTests(unittest.TestCase):
    def test_relative_rows_ports_and_euler_are_preserved(self):
        raw, basis = interior_vertex_torus()
        for name, rows in [('empty', [[0]*7 for _ in raw['tetrahedra']])] + list(basis.items()):
            with self.subTest(surface=name):
                parallelity = normal_cut_parallelity(raw, rows)
                geometry = parallelity['geometry']
                before = deepcopy(geometry)
                reduced, proof, stats = reduce_core_top_handles(raw, rows, geometry)
                self.assertEqual(stats['cancelled_23'], len(geometry['core']['handles3']))
                self.assertEqual(reduced['core']['handles3'], [])
                self.assertEqual(reduced, replay_core_top_reduction(raw, rows, geometry, proof))
                self.assertEqual(geometry, before)
                for field in ('ports', 'gluings', 'free_edges', 'polygons', 'source', 'coordinates'):
                    self.assertEqual(reduced[field], geometry[field])
                for dimension in (0, 1):
                    self.assertEqual(reduced['core'][f'handles{dimension}'],
                                     geometry['core'][f'handles{dimension}'])
                for i, old in enumerate(proof['surviving_two_handles']):
                    self.assertEqual(reduced['core']['handles2'][i],
                                     dict(geometry['core']['handles2'][old], id=i))
                euler = lambda core: sum((-1)**i * len(core[f'handles{i}']) for i in range(4))
                self.assertEqual(euler(reduced['core']), euler(geometry['core']))

    def test_positive_rescaling_preserves_the_top_schedule(self):
        raw, basis = interior_vertex_torus()
        schedules = []
        for multiplier in (1, 2, 1 << 4096):
            rows = [[multiplier*x for x in row] for row in basis['mobius']]
            geometry = normal_cut_parallelity(raw, rows)['geometry']
            _, proof, _ = reduce_core_top_handles(raw, rows, geometry)
            self.assertIsNotNone(replay_core_top_reduction(raw, json_safe(rows), geometry, proof))
            schedules.append((proof['moves'], proof['surviving_two_handles']))
        self.assertTrue(all(value == schedules[0] for value in schedules))

    def test_real_interior_loop_is_not_a_single_contact(self):
        raw = _interior_loop_torus()
        rows = [[0]*7 for _ in raw['tetrahedra']]
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        incidence = source_core_top_incidence(raw, rows, geometry)
        loops = [h for h in incidence['two_handles']
                 if h['ends'][0] is not None and h['ends'][0] == h['ends'][1]]
        self.assertTrue(loops)
        _, proof, _ = reduce_core_top_handles(raw, rows, geometry)
        for loop in loops:
            bad = deepcopy(proof)
            bad['moves'] = [[loop['id'], loop['ends'][0]]]
            bad['surviving_two_handles'] = [i for i in range(len(incidence['two_handles']))
                                            if i != loop['id']]
            self.assertIsNone(replay_core_top_reduction(raw, rows, geometry, bad))
        self.assertIsNotNone(replay_core_top_reduction(raw, rows, geometry, proof))

    def test_bad_move_ids_rank_inventory_and_source_binding_are_rejected(self):
        raw, basis = interior_vertex_torus()
        rows = [[5*x for x in row] for row in basis['mobius']]
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        _, proof, _ = reduce_core_top_handles(raw, rows, geometry)
        bad_proofs = []
        for key, value in [('schema', 'other'), ('input_sha256', '0'*64),
                           ('moves', []), ('moves', [[-1, 0]]),
                           ('moves', [[proof['moves'][0][0], False]]),
                           ('surviving_two_handles', [])]:
            bad = deepcopy(proof)
            bad[key] = value
            bad_proofs.append(bad)
        bad = deepcopy(proof)
        bad['moves'].append(bad['moves'][0])
        bad_proofs.append(bad)
        for bad in bad_proofs:
            self.assertIsNone(replay_core_top_reduction(raw, rows, geometry, bad))
        bad_geometry = deepcopy(geometry)
        changed = next(h for h in bad_geometry['core']['handles2'] if h['rank'] > 1)
        changed['rank'] = 1
        self.assertIsNone(replay_core_top_reduction(raw, rows, bad_geometry, proof))
        bad_geometry = deepcopy(geometry)
        bad_geometry['core']['handles3'][0]['id'] = False
        self.assertIsNone(replay_core_top_reduction(raw, rows, bad_geometry, proof))

    def test_old_three_handle_cases_have_seven_certified_censuses(self):
        root = Path(__file__).parents[2]
        reference = json.loads((root/'synthesis/data/core-three-handle-probe.json').read_text())
        expected = {c['id']: c for c in reference['cases']}
        bank = json.loads((root/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
        completed = 0
        for case in bank:
            if case['id'] not in expected:
                continue
            with self.subTest(case=case['id']):
                raw, rows = case['triangulation'], case['coordinates']
                result = normal_cut_handlebodies(raw, rows, record_certificate=True)
                self.assertEqual(result['stats']['top_reduction']['cancelled_23'],
                                 expected[case['id']]['source_three_handles'])
                if result['status'] == 'COMPLETE':
                    completed += 1
                    self.assertEqual(result['certificate']['schema'], 'normal-cut-handlebodies-v6')
                    self.assertEqual(result['census']['histogram'], expected[case['id']]['oracle_histogram'])
                    self.assertTrue(verify_normal_cut_handlebodies(raw, rows, result['certificate']))
                else:
                    self.assertFalse(expected[case['id']]['kernel_eliminates_all_rows'])
        self.assertEqual(completed, 7)

    def test_whole_cut_replay_imports_no_top_producer(self):
        raw, basis = interior_vertex_torus()
        rows = basis['boundary_disk']
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        targets = (
            'fastunknot.core_top_reduction.source_core_top_incidence',
            'fastunknot.core_top_reduction.rooted_top_plan',
            'fastunknot.core_top_reduction.reduce_core_top_handles',
            'fastunknot.normal_cut_handlebodies.reduce_core_top_handles',
            'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'fastunknot.normal_parallelity_geometry._parallelity_geometry',
        )
        with ExitStack() as stack:
            for name in targets:
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof))

    def test_whole_cut_wrapper_rejects_omission_downgrade_and_forgery(self):
        raw, basis = interior_vertex_torus()
        rows = [[3*x for x in row] for row in basis['boundary_disk']]
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        for field in ('top_reduction', 'terminal'):
            bad = deepcopy(proof)
            bad.pop(field)
            self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        for change in ('none', 'nested', 'source', 'rank', 'downgrade'):
            bad = deepcopy(proof)
            if change == 'none':
                bad['top_reduction'] = None
            elif change == 'nested':
                bad['terminal']['schema'] = 'normal-cut-handlebodies-v6'
            elif change == 'source':
                bad['terminal']['parallelity'] = bad['parallelity']
            elif change == 'rank':
                bad['parallelity']['geometry']['core']['handles2'][0]['rank'] += 1
            else:
                bad = dict(bad['terminal'], parallelity=bad['parallelity'],
                           boundary=bad['boundary'], census=bad['census'])
            self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, proof, max_operations=0))

    def test_callbacks_and_no_three_handle_legacy_path(self):
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('cancelled')
        raw, basis = interior_vertex_torus()
        rows = basis['mobius']
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        _, proof, _ = reduce_core_top_handles(raw, rows, geometry)
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            reduce_core_top_handles(raw, rows, geometry, check=Cancel())
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            replay_core_top_reduction(raw, rows, geometry, proof, check=Cancel())
        old_raw, old_rows = layered_torus(2)
        result = normal_cut_handlebodies(old_raw, old_rows, record_certificate=True)
        self.assertNotIn('top_reduction', result['stats'])
        self.assertNotEqual(result['certificate']['schema'], 'normal-cut-handlebodies-v6')
        self.assertTrue(verify_normal_cut_handlebodies(old_raw, old_rows, result['certificate']))

    def test_multiple_interior_vertices_and_dependent_root_order(self):
        try:
            import regina
        except ImportError:
            self.skipTest('optional independent Regina source construction')
        from normal_orbit_research.fixtures import regina_triangulation, export_triangulation
        raw, _ = layered_torus(1)
        triangulation = regina_triangulation(raw)
        for _ in range(5):
            tetrahedron = min(triangulation.tetrahedra(), key=lambda t:
                (sum(t.vertex(v).isBoundary() for v in range(4)), t.index()))
            self.assertTrue(triangulation.pachner(tetrahedron))
        raw = export_triangulation(triangulation)
        rows = [[0]*7 for _ in raw['tetrahedra']]
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        incidence = source_core_top_incidence(raw, rows, geometry)
        self.assertEqual(len(incidence['three_handles']), 5)
        reduced, proof, stats = reduce_core_top_handles(raw, rows, geometry)
        self.assertEqual(reduced, replay_core_top_reduction(raw, rows, geometry, proof))
        self.assertLessEqual(stats['incidence_visits'], 2*len(incidence['two_handles']))
        dependent = next(move for move in proof['moves']
                         if all(v is not None for v in incidence['two_handles'][move[0]]['ends']))
        bad = deepcopy(proof)
        bad['moves'].remove(dependent)
        bad['moves'].insert(0, dependent)
        self.assertIsNone(replay_core_top_reduction(raw, rows, geometry, bad))
        result = normal_cut_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['census']['histogram'], [dict(genus=1, multiplicity=1)])
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, result['certificate']))
        self.assertTrue(regina.Triangulation3(triangulation).isSolidTorus())


if __name__ == '__main__':
    unittest.main()
