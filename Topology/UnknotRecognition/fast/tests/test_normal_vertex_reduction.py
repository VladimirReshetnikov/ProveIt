"""Native expanded-edge witnesses, canonical peeling and source-bound descent."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.boundary_shellings import shell_boundary
from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_sector import SearchLimit
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _EDGES, _edge, NormalOrbitError
from fastunknot.normal_vertex_reduction import vertex_reduction_ray
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


# A labelled finite solid-torus refinement. Its linking edge appears twice in
# one local face; expansion creates double triangles and a separate interior
# vertex-link sphere. The raw vector was independently compared with Regina's
# edge.linkingSurface() in the research audit; no Regina is needed by this test.
EXPANDED_LINK_SOURCE = [
    [(13, [1, 3, 2, 0]), (10, [2, 3, 0, 1]), (13, [1, 3, 2, 0]), (13, [1, 3, 2, 0])],
    [(11, [2, 0, 3, 1]), (2, [3, 2, 1, 0]), (9, [1, 2, 0, 3]), (7, [0, 3, 1, 2])],
    [(11, [1, 2, 0, 3]), (7, [2, 0, 3, 1]), (1, [3, 2, 1, 0]), (3, [0, 2, 1, 3])],
    [(12, [0, 2, 1, 3]), (11, [1, 0, 3, 2]), (4, [1, 3, 0, 2]), (2, [0, 2, 1, 3])],
    [(3, [2, 0, 3, 1]), (12, [0, 1, 3, 2]), (7, [0, 2, 1, 3]), None],
    [(12, [2, 0, 1, 3]), (7, [2, 3, 0, 1]), (9, [3, 0, 2, 1]), None],
    [(8, [3, 2, 1, 0]), (8, [3, 2, 1, 0]), (13, [2, 0, 3, 1]), (10, [0, 1, 3, 2])],
    [(2, [1, 3, 0, 2]), (4, [0, 2, 1, 3]), (1, [0, 2, 3, 1]), (5, [2, 3, 0, 1])],
    [(10, [0, 3, 1, 2]), (9, [2, 1, 3, 0]), (6, [3, 2, 1, 0]), (6, [3, 2, 1, 0])],
    [(1, [2, 0, 1, 3]), (8, [3, 1, 0, 2]), (5, [1, 3, 2, 0]), (10, [0, 3, 2, 1])],
    [(8, [0, 2, 3, 1]), (9, [0, 3, 2, 1]), (6, [0, 1, 3, 2]), (0, [2, 3, 0, 1])],
    [(3, [1, 0, 3, 2]), (2, [2, 0, 1, 3]), (1, [1, 3, 0, 2]), None],
    [(3, [0, 2, 1, 3]), (4, [0, 1, 3, 2]), (5, [1, 2, 0, 3]), None],
    [(0, [3, 0, 2, 1]), (0, [3, 0, 2, 1]), (0, [3, 0, 2, 1]), (6, [1, 3, 0, 2])],
]
EXPECTED_RAW_LINK = [
    [0, 1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0], [1, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0],
    [0, 0, 2, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0, 0],
    [0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 2, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0],
    [1, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
]


def expanded_source():
    return dict(tetrahedra=[[None if entry is None else dict(
        tetrahedron=entry[0], permutation=list(entry[1])) for entry in row]
        for row in EXPANDED_LINK_SOURCE])


class VertexReductionTests(unittest.TestCase):
    def assert_positive(self, source, result):
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        prepared = _prepare(source, lambda: None)
        self.assertEqual(result['stats']['vertex_count'], prepared['vertices'])
        raw = _coordinates(prepared, result['raw_coordinates'], lambda: None)
        canonical = _coordinates(prepared, result['canonical_coordinates'], lambda: None)
        self.assertGreater(canonical['euler_characteristic'], 0)
        self.assertLessEqual(raw['normal_disks'], 4*len(source['tetrahedra']))
        self.assertTrue(all(type(x) is int and 0 <= x <= 2
                            for row in result['raw_coordinates'] for x in row))
        minima = {}
        for c, v in enumerate(prepared['vertex_roots']):
            value = result['canonical_coordinates'][c//4][c % 4]
            minima[v] = min(minima.get(v, value), value)
        self.assertFalse(any(minima.values()))
        for canonical_row, ray_row in zip(result['canonical_coordinates'], result['coordinates']):
            for x, y in zip(canonical_row, ray_row):
                self.assertIs(type(y), int)
                if not x:
                    self.assertEqual(y, 0)
        packet = crush_normal_ray(source, result['coordinates'])['certificate']
        self.assertTrue(verify_normal_crushing(source, packet))
        if packet['successor'] is not None:
            self.assertLess(len(packet['successor']['tetrahedra']), len(source['tetrahedra']))
        return packet

    def test_one_vertex_is_a_source_observation_without_search_or_knot_verdict(self):
        for count in (1, 7):
            source, _ = layered_torus(count)
            with patch('fastunknot.normal_vertex_reduction.extract_positive_ray', side_effect=AssertionError):
                result = vertex_reduction_ray(source)
            self.assertEqual(result['status'], 'ONE_VERTEX')
            self.assertEqual(result['stats']['vertex_count'], 1)
            self.assertEqual(result['stats']['descent_steps'], 0)
            self.assertIsNone(result['coordinates'])
            self.assertIsNone(result['raw_coordinates'])

    def test_boundary_and_boundary_to_interior_edge_choices_are_native(self):
        cap, _ = boundary_cap(*layered_torus(1))
        interior, _ = interior_vertex_torus()
        for source, boundary_count in ((cap, 2), (interior, 1)):
            with patch('fastunknot.normal_sector.sector_rays', side_effect=AssertionError), \
                 patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
                result = vertex_reduction_ray(source)
            self.assertEqual(result['diagnostics']['boundary_vertices'], boundary_count)
            self.assertNotEqual(*result['diagnostics']['seed_endpoints'])
            packet = self.assert_positive(source, result)
            self.assertEqual(len(packet['successor']['tetrahedra']), 1)

    def test_expansion_counts_repeated_face_edge_occurrences_and_peels_only_links(self):
        source = expanded_source()
        result = vertex_reduction_ray(source)
        self.assertEqual(result['raw_coordinates'], EXPECTED_RAW_LINK)
        self.assertEqual(result['diagnostics']['face_additions'], [33, 1, 26])
        self.assertEqual(result['stats']['raw_euler'], 3)
        self.assertEqual(result['stats']['canonical_euler'], 1)
        self.assertEqual(result['stats']['peeled_vertex_links'], 1)
        self.assertEqual(result['stats']['maximum_raw_coordinate'], 2)
        prepared = _prepare(source, lambda: None)
        t, f = divmod(result['diagnostics']['face_additions'][0], 4)
        incident = [prepared['edge_roots'][_edge(t, a, b)]
                    for a, b in _EDGES if f not in (a, b)]
        seed = result['diagnostics']['seed_edge']
        self.assertEqual(incident.count(seed), 2)
        self.assertEqual(sum(e == seed for e in set(incident)), 1)
        canonical = deepcopy(EXPECTED_RAW_LINK)
        canonical[0][1] = canonical[13][3] = 0
        self.assertEqual(result['canonical_coordinates'], canonical)
        self.assert_positive(source, result)

    def test_complete_preprocessing_reuses_the_existing_authenticated_chain_schema(self):
        for name, diagram, final_tetrahedra in (
                ('circle', Diagram.from_pd([]), 0),
                ('trefoil', Diagram.from_braid(2, [1, 1, 1]), 10)):
            initial = diagram_exterior(diagram)
            shelled = shell_boundary(initial)
            shelling = {k: shelled[k] for k in ('triangulation', 'moves')}
            current, steps = shelling['triangulation'], []
            while current is not None:
                result = vertex_reduction_ray(current)
                if result['status'] == 'ONE_VERTEX':
                    break
                packet = self.assert_positive(current, result)
                steps.append(packet)
                current = packet['successor']
                self.assertLessEqual(len(steps), len(shelling['triangulation']['tetrahedra']))
            self.assertEqual(0 if current is None else len(current['tetrahedra']), final_tetrahedra, name)
            chain = dict(schema='diagram-crushing-v1', input_pd=[list(r) for r in diagram.pd],
                source_triangulation=initial, shelling=shelling, steps=steps,
                status='UNKNOT' if current is None else 'REDUCED', triangulation=current)
            self.assertTrue(verify_crushing_chain(diagram, chain))

    def test_source_and_output_are_exact_deterministic_and_unmodified(self):
        source = expanded_source()
        before = deepcopy(source)
        result = vertex_reduction_ray(source)
        self.assertEqual(source, before)
        self.assertEqual(vertex_reduction_ray(source), result)
        self.assertNotIn('certificate', result)
        for malformed in (None, [], {}, {'tetrahedra': []}, {'tetrahedra': [[None]*4]}):
            with self.assertRaises(ValueError):
                vertex_reduction_ray(malformed)
        for value in (True, 0.5, '13', -1):
            bad = deepcopy(source)
            bad['tetrahedra'][0][0]['tetrahedron'] = value
            with self.assertRaises(ValueError):
                vertex_reduction_ray(bad)
        bad = deepcopy(source)
        bad['tetrahedra'][0][0]['permutation'][0] = True
        with self.assertRaises(ValueError):
            vertex_reduction_ray(bad)

    def test_cancellation_identity_survives_source_closure_peeling_and_extraction(self):
        source = expanded_source()
        calls = [0]
        def count():
            calls[0] += 1
        vertex_reduction_ray(source, check=count)
        for error_type in (ValueError, TypeError, NormalOrbitError, SearchLimit, RuntimeError):
            for stop in (1, calls[0]//3, 2*calls[0]//3, calls[0]):
                error = error_type('caller cancellation')
                current = [0]
                def check():
                    current[0] += 1
                    if current[0] == stop:
                        raise error
                with self.assertRaises(error_type) as raised:
                    vertex_reduction_ray(source, check=check)
                self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
