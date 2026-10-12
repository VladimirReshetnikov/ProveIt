"""Geometric cap incidence, multiple 3-handles, and hostile certificate replay."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _edge
from fastunknot.source_core_dual import source_core_dual_graph, source_core_dual_reduction
from fastunknot.source_core_dual_verify import replay_source_core_dual
from normal_orbit_research.fixtures import interior_vertex_torus, layered_torus
from source_core_dual_research.fixtures import stellar_torus


class SourceCoreDualTests(unittest.TestCase):
    def packet(self, raw, rows):
        return normal_cut_parallelity(raw, rows, record_certificate=True)

    def test_native_oriented_cap_occurrences_on_all_corpus_sources(self):
        corpus = Path(__file__).parents[1] / 'marked_parallelity_research/corpus.json'
        cases = json.loads(corpus.read_text())['cases']
        flipped = loops = inspected = 0
        for case in cases:
            prepared = _prepare(case['triangulation'], lambda: None)
            analysed = _coordinates(prepared, case['coordinates'], lambda: None)
            geometry = _parallelity_geometry(prepared, analysed, lambda: None)
            owner = {h['vertex']: h['id'] for h in geometry['core']['handles3']}
            expected = []
            for h in geometry['core']['handles2']:
                flag = h['cycle'][0]
                t, (a, b) = flag['tetrahedron'], flag['local_edge']
                local = _edge(t, a, b)
                ends = [owner.get(prepared['vertex_roots'][4*t+v], -1) for v in (a, b)]
                if prepared['edge_orientations'][local]:
                    ends.reverse()
                    flipped += 1
                w = analysed['weights'][h['edge']]
                if w:
                    if h['rank'] == 0:
                        ends[1] = -1
                    else:
                        self.assertEqual(h['rank'], w)
                        ends[0] = -1
                loops += ends[0] == ends[1]
                expected.append(dict(two_handle=h['id'], ends=ends))
                inspected += 1
            self.assertEqual(source_core_dual_graph(geometry)['edges'], expected)
        self.assertGreater(flipped, 0)
        self.assertGreater(loops, 0)
        self.assertGreater(inspected, 100)

    def test_multiple_interior_vertices_and_reversed_forest_order(self):
        for count in (1, 2, 4, 8, 16):
            raw, rows = stellar_torus(count)
            packet = self.packet(raw, rows)
            original = deepcopy(packet['geometry'])
            reduced, proof, stats = source_core_dual_reduction(original)
            self.assertEqual(stats['removed_three_handles'], count)
            self.assertEqual(stats['removed_two_handles'], count)
            self.assertEqual(stats['adjacency_visits'], 2 * stats['dual_edge_visits'])
            proof['forest'].reverse()
            self.assertEqual(replay_source_core_dual(original, proof), reduced)
            self.assertEqual(packet['geometry'], original)
            self.assertEqual(reduced['ports'], original['ports'])
            self.assertEqual(reduced['core']['handles0'], original['core']['handles0'])
            self.assertEqual(reduced['core']['handles1'], original['core']['handles1'])
            self.assertEqual(sum((-1)**i * len(original['core'][f'handles{i}']) for i in range(4)),
                             sum((-1)**i * len(reduced['core'][f'handles{i}']) for i in range(4)))
            result = normal_cut_handlebodies(raw, rows, record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['census']['histogram'], [dict(genus=1, multiplicity=1)])
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, result['certificate']))

    def test_native_unmarked_ports_and_one_sided_cut(self):
        raw, basis = interior_vertex_torus()
        for name, expected in (
                ('boundary_disk', [dict(genus=0, multiplicity=1), dict(genus=1, multiplicity=1)]),
                ('mobius', [dict(genus=1, multiplicity=1)])):
            result = normal_cut_handlebodies(raw, basis[name], record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['certificate']['schema'], 'normal-cut-handlebodies-v6')
            self.assertEqual(result['census']['histogram'], expected)
            self.assertTrue(verify_normal_cut_handlebodies(raw, basis[name], result['certificate']))

    def test_spherical_cut_does_not_infer_a_handlebody_from_homology(self):
        raw, basis = interior_vertex_torus()
        result = normal_cut_handlebodies(raw, basis['sphere'], record_certificate=True)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'dual_reduced_boundary_kernel_stalled')

    def test_positive_scaling_invariance_and_huge_binary_census(self):
        raw, basis = interior_vertex_torus()
        first = self.packet(raw, basis['mobius'])
        n = 1 << 4096
        rows = [[n * v for v in row] for row in basis['mobius']]
        second = self.packet(raw, rows)
        self.assertEqual(source_core_dual_graph(first['geometry']),
                         source_core_dual_graph(second['geometry']))
        result = normal_cut_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['census']['histogram'], [dict(genus=1, multiplicity=n//2+1)])
        encoded = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify_normal_cut_handlebodies(raw, json_safe(rows), encoded))

    def test_independent_replay_with_all_producers_disabled(self):
        raw, basis = interior_vertex_torus()
        rows = [[3 * x for x in row] for row in basis['mobius']]
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        names = (
            'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            'fastunknot.normal_cut_dual.finish_dual_cut',
            'fastunknot.source_core_dual.source_core_dual_graph',
            'fastunknot.source_core_dual.source_core_dual_reduction',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words',
            'fastunknot.bundle_boundary_kernel.bundle_boundary_kernel',
        )
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof))

    def test_forest_mutations_and_source_geometry_mutations_are_rejected(self):
        raw, basis = interior_vertex_torus()
        rows = basis['boundary_disk']
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        for forest in ([], [True], [-1], [10**9], ['garbage'], proof['dual']['forest'] * 2):
            bad = deepcopy(proof)
            bad['dual']['forest'] = forest
            self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['dual']['forest'][0] = hex(bad['dual']['forest'][0])
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['dual']['extra'] = 1
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['parallelity']['geometry']['core']['handles3'][0]['link_triangles'].pop()
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['parallelity']['geometry']['core']['handles2'][0]['rank'] += 1
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))
        bad = deepcopy(proof)
        bad['census']['histogram'][0]['genus'] += 1
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, bad))

    def test_selected_dual_loops_are_rejected(self):
        raw, basis = interior_vertex_torus()
        packet = self.packet(raw, basis['boundary_disk'])
        geometry = packet['geometry']
        graph = source_core_dual_graph(geometry)
        loops = [e['two_handle'] for e in graph['edges'] if e['ends'][0] == e['ends'][1]]
        self.assertTrue(loops)
        for e in loops:
            self.assertIsNone(replay_source_core_dual(geometry,
                dict(schema='source-core-dual-forest-v1', forest=[e])))

    def test_no_three_handles_keep_the_established_certificate_path(self):
        raw, rows = layered_torus(2)
        result = normal_cut_handlebodies(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertNotEqual(result['certificate']['schema'], 'normal-cut-handlebodies-v6')
        self.assertNotIn('dual_core', result['stats'])

    def test_callbacks_and_operation_caps(self):
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('cancelled')
        raw, basis = interior_vertex_torus()
        rows = [[3*x for x in row] for row in basis['mobius']]
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            normal_cut_handlebodies(raw, rows, check=Cancel())
        proof = normal_cut_handlebodies(raw, rows, record_certificate=True)['certificate']
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            verify_normal_cut_handlebodies(raw, rows, proof, check=Cancel())
        self.assertFalse(verify_normal_cut_handlebodies(raw, rows, proof, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(raw, rows, max_cycles=0)['status'], 'INCONCLUSIVE')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proof, max_operations=100000))


if __name__ == '__main__':
    unittest.main()
