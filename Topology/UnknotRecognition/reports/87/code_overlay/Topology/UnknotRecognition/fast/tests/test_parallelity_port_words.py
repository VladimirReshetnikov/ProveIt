"""Cyclic port order, relative fibre gauges, and source-bound replay."""

from contextlib import ExitStack
from copy import deepcopy
from itertools import combinations
import importlib.util
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.parallelity_port_words import (
    normal_parallelity_port_words, _port_queries, _boundary_words, _fibre_gauges,
)
from fastunknot.parallelity_port_words_verify import verify_parallelity_port_words
from fastunknot.weighted_orbits import weighted_orbit_histogram
from normal_orbit_research.fixtures import layered_torus
from parallelity_port_research import (
    literal_port_words, _disabled_producer_replay, validate_product_templates,
)
from tests.test_normal_surface_orbits import relabel


ROOT = Path(__file__).resolve().parents[2]


def trace_length(certificate):
    total = 0
    for field in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
        part = certificate['source'][field]
        if field.endswith('selector'):
            part = part['weighted_certificate']
        total += len(part['orbit_proof']['operations'])
    for field in ('port_paths', 'port_fibres'):
        total += len(certificate[field]['orbit_proof']['operations'])
    return total


def polygon_disc(marked, *, loop=False):
    """Small genuine polygon quotients, including a one-edge boundary circle."""
    degree = 3 if loop else len(marked)
    polygon = dict(kind='prism', start=0, stop=1, edges=list(range(degree)),
                   vertices=list(range(degree)), corner_starts=list(range(degree)))
    gluings = []
    free = []
    if loop:
        gluings.append(dict(left=0, right=0, left_edge=0, right_edge=1,
                            left_map=[1, -1], right_map=[1, -1], rank_start=1,
                            rank_stop=2, ends_reverse=True, fibre_flip=False))
        free.append(dict(polygon=0, edge=2, rank_start=1, rank_stop=2,
                         original_boundary=False, port=0))
        q = 1
    else:
        q = 0
        for edge, is_port in enumerate(marked):
            record = dict(polygon=0, edge=edge, rank_start=1, rank_stop=2,
                          original_boundary=not is_port)
            if is_port:
                record['port'] = q
                q += 1
            free.append(record)
    return dict(polygons=[polygon], gluings=gluings, free_edges=free,
                ports=[{} for _ in range(q)], polygon_points=1, corner_points=degree)


class ParallelityPortTests(unittest.TestCase):
    def checked(self, raw, rows):
        result = normal_parallelity_port_words(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(verify_parallelity_port_words(raw, rows, result['certificate']))
        reference = literal_port_words(result['geometry'], result['summary']['base_profiles'])
        self.assertEqual(result['boundary_words'], reference['boundary_words'])
        self.assertEqual(result['fibre_gauges'], reference['fibre_gauges'])
        self.assertLessEqual(sum(len(t['product_tetrahedra']) for t in result['disc_templates']),
                             9 * len(result['geometry']['ports']))
        return result

    def test_empty_single_port_adjacent_and_repeated_boundary_vertex(self):
        for marked in ([False] * 3, [True, False, False], [True] * 4,
                       [True, True, False, True, False, False]):
            geometry = polygon_disc(marked)
            self._check_disc_geometry(geometry)
        result = self._check_disc_geometry(polygon_disc([], loop=True))
        self.assertEqual(result, [[dict(port=0, entry_endpoint=0, original_edges_after=0)]])

    def _check_disc_geometry(self, geometry):
        paths, weights, cover, fibre_weights = _port_queries(geometry, lambda: None)
        boundary = weighted_orbit_histogram(geometry['corner_points'], paths, weights, dimension=2)
        number = len(geometry['ports'])
        words = _boundary_words(boundary['histogram'], number, lambda: None)
        profiles = [dict(core_ports=list(range(number)), product=True)]
        fibre = weighted_orbit_histogram(2, cover, fibre_weights, dimension=1)
        gauges = _fibre_gauges(fibre['histogram'], profiles, number, lambda: None)
        reference = literal_port_words(geometry, profiles)
        self.assertEqual(words, reference['boundary_words'])
        self.assertEqual(gauges, reference['fibre_gauges'])
        return words

    def test_layered_meridians_and_relabelled_charts(self):
        rng = random.Random(26101237)
        for tetrahedra in (1, 2, 4):
            raw, base = layered_torus(tetrahedra)
            for multiplier in (0, 1, 2, 5):
                rows = [[multiplier * x for x in row] for row in base]
                self.checked(raw, rows)
            for _ in range(3):
                changed, rows = relabel(raw, [[3 * x for x in row] for row in base], rng)
                self.checked(changed, rows)

    def test_source_single_two_handle_disc_and_zero_gaps(self):
        raw, _ = layered_torus(2)
        rows = [[0, 0, 1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]]
        result = self.checked(raw, rows)
        self.assertEqual(len(result['boundary_words']), 1)
        self.assertEqual(len(result['boundary_words'][0]), 8)
        self.assertTrue(all(row['original_edges_after'] == 0
                            for row in result['boundary_words'][0]))
        self.assertEqual(len(result['disc_templates']), 1)
        self.assertEqual(len(result['disc_templates'][0]['product_tetrahedra']), 24)

    def test_one_sided_and_disconnected_fibre_data(self):
        raw, _ = layered_torus(1)
        for links in range(3):
            for mobius in range(1, 7):
                self.checked(raw, [[links] * 4 + [0, mobius, 0]])

    def test_saved_source_topologies(self):
        bank = json.loads((ROOT / 'synthesis/data/parallelity-audit.json').read_text())
        tested = 0
        for record in bank['source_proofs']:
            if record['id'].startswith('binary/'):
                continue
            self.checked(record['triangulation'], record['coordinates'])
            tested += 1
            if tested >= 32:
                break
        self.assertGreaterEqual(tested, 32)

    def test_product_triangulations_have_spherical_boundaries(self):
        raw, rows = layered_torus(4)
        result = self.checked(raw, [[3 * x for x in row] for row in rows])
        for template in result['disc_templates']:
            cells = template['product_tetrahedra']
            vertices, edges, faces = set(), set(), {}
            for tetrahedron in cells:
                self.assertEqual(len(set(tetrahedron)), 4)
                vertices.update(tetrahedron)
                edges.update(tuple(sorted(e)) for e in combinations(tetrahedron, 2))
                for face in combinations(tetrahedron, 3):
                    key = tuple(sorted(face))
                    faces[key] = faces.get(key, 0) + 1
            self.assertTrue(all(count in (1, 2) for count in faces.values()))
            self.assertEqual(len(vertices) - len(edges) + len(faces) - len(cells), 1)
            boundary_faces = [face for face, count in faces.items() if count == 1]
            boundary_edges = {tuple(sorted(edge)) for face in boundary_faces
                              for edge in combinations(face, 2)}
            boundary_vertices = {vertex for face in boundary_faces for vertex in face}
            self.assertEqual(len(boundary_vertices) - len(boundary_edges) + len(boundary_faces), 2)
        if importlib.util.find_spec('regina') is not None:
            validation = validate_product_templates(result['disc_templates'])
            self.assertEqual(validation['templates_checked'], len(result['disc_templates']))
            self.assertTrue(all(c['is_ball'] for c in validation['complexes']))

    def test_huge_binary_source_json_and_disabled_producer_replay(self):
        raw, base = layered_torus(2)
        rows = [[(1 << 16384) * x for x in row] for row in base]
        result = normal_parallelity_port_words(raw, rows, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(len(result['geometry']['ports']), 2)
        wire = json.loads(json.dumps(json_safe(result['certificate'])))
        _disabled_producer_replay(raw, json_safe(rows), wire)
        self.assertLess(len(json.dumps(json_safe(result['disc_templates']))), 20000)
        with self.assertRaises(ValueError):
            literal_port_words(result['geometry'], result['summary']['base_profiles'])

    def test_forged_words_gaps_gauges_source_and_template_rejected(self):
        raw, rows = layered_torus(2)
        rows = [[3 * x for x in row] for row in rows]
        proof = normal_parallelity_port_words(raw, rows, record_certificate=True)['certificate']
        bad = []
        for field in ('port', 'entry_endpoint', 'original_edges_after'):
            changed = deepcopy(proof)
            changed['boundary_words'][0][0][field] += 1
            bad.append(changed)
        changed = deepcopy(proof)
        changed['fibre_gauges'][0]['gauges'][0][1] ^= 1
        bad.append(changed)
        changed = deepcopy(proof)
        changed['disc_templates'][0]['product_tetrahedra'][0][0] += 1
        bad.append(changed)
        changed = deepcopy(proof)
        changed['disc_templates'][0]['boundary_sides'][0]['parameter'] = [0, 2, 1]
        bad.append(changed)
        changed = deepcopy(proof)
        changed['source']['geometry']['ports'][0]['core_handle'] += 1
        bad.append(changed)
        changed = deepcopy(proof)
        changed['port_paths']['histogram'][0]['weight'][0] = True
        bad.append(changed)
        changed = deepcopy(proof)
        changed['extra'] = 1
        bad.append(changed)
        for changed in bad:
            self.assertFalse(verify_parallelity_port_words(raw, rows, changed))

    def test_endpoint_bit_collisions_cannot_carry_into_valid_partition(self):
        with self.assertRaises(ArithmeticError):
            _boundary_words([dict(weight=[3, 0], orbits=1),
                             dict(weight=[3, 1], orbits=1)], 2, lambda: None)
        with self.assertRaises(ArithmeticError):
            _boundary_words([dict(weight=[15, 0], orbits=1)], 2, lambda: None)

    def test_shared_caps_and_cancellation(self):
        raw, rows = layered_torus(2)
        result = normal_parallelity_port_words(raw, rows, record_certificate=True)
        cycles = sum(s['orbit_cycles'] for s in result['stats']['source'].values())
        cycles += sum(result['stats'][name]['orbit_cycles'] for name in ('port_paths', 'port_fibres'))
        for cap in (0, cycles - 1):
            interrupted = normal_parallelity_port_words(raw, rows, max_cycles=cap,
                                                        record_certificate=True)
            self.assertEqual(interrupted['status'], 'INCONCLUSIVE')
            for field in ('geometry', 'boundary_words', 'disc_templates', 'certificate'):
                self.assertNotIn(field, interrupted)
        self.assertEqual(normal_parallelity_port_words(raw, rows, max_cycles=cycles)['boundary_words'],
                         result['boundary_words'])
        operations = trace_length(result['certificate'])
        self.assertFalse(verify_parallelity_port_words(raw, rows, result['certificate'],
                                                       max_operations=operations - 1))
        self.assertTrue(verify_parallelity_port_words(raw, rows, result['certificate'],
                                                      max_operations=operations))
        def cancel():
            raise ValueError('cancelled')
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            normal_parallelity_port_words(raw, rows, check=cancel)
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            verify_parallelity_port_words(raw, rows, result['certificate'], check=cancel)


if __name__ == '__main__':
    unittest.main()
