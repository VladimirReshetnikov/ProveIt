"""Literal boundary walks, unique-token bounds, source replay and hostile proofs."""

from collections import defaultdict
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


ROOT = Path(__file__).resolve().parents[2]


class _ParityUnion:
    def __init__(self, size):
        self.parent = list(range(size))
        self.parity = [0] * size

    def find(self, point):
        if self.parent[point] != point:
            root, parity = self.find(self.parent[point])
            self.parity[point] ^= parity
            self.parent[point] = root
        return self.parent[point], self.parity[point]

    def join(self, left, right, flip=0):
        a, pa = self.find(left)
        b, pb = self.find(right)
        if a == b:
            if pa ^ pb != flip:
                raise AssertionError('inconsistent literal fibre chart')
        else:
            self.parent[a] = b
            self.parity[a] = pa ^ pb ^ flip


def literal_interfaces(g, max_points=100000):
    """Expand actual free-edge incidences and walk old arcs one at a time."""
    n = g['corner_points']
    if n > max_points:
        raise ValueError('literal oracle point cap')
    corners = _ParityUnion(n)
    for link in g['gluings']:
        p, q = g['polygons'][link['left']], g['polygons'][link['right']]
        for rank in range(link['rank_start'], link['rank_stop']):
            left = link['left_map'][0] * rank + link['left_map'][1] - p['start']
            right = link['right_map'][0] * rank + link['right_map'][1] - q['start']
            for end in (0, 1):
                i = (link['left_edge'] + end) % len(p['vertices'])
                j = (link['right_edge'] + (end ^ link['ends_reverse'])) % len(q['vertices'])
                corners.join(p['corner_starts'][i] + left,
                             q['corner_starts'][j] + right, int(link['fibre_flip']))
    graph, edges, tokens = defaultdict(list), [], {}
    for free in g['free_edges']:
        p = g['polygons'][free['polygon']]
        for rank in range(free['rank_start'], free['rank_stop']):
            ends = [p['corner_starts'][(free['edge'] + end) % len(p['vertices'])] + rank - 1
                    for end in (0, 1)]
            index = len(edges)
            port = None if free['original_boundary'] else free['port']
            edges.append((ends, port))
            for side, point in enumerate(ends):
                root, _ = corners.find(point)
                graph[root].append((index, side))
                if port is not None:
                    tokens[2 * port + side] = (index, side)
    if any(len(ends) != 2 for ends in graph.values()):
        raise AssertionError('literal base boundary is not a one-manifold')
    gaps = []
    for token, (edge, side) in sorted(tokens.items()):
        initial = edges[edge][0][side]
        vertex, state = corners.find(initial)
        previous, count, visited = (edge, side), 0, set()
        while True:
            next_edge, next_side = next(flag for flag in graph[vertex] if flag != previous)
            points, port = edges[next_edge]
            if port is not None:
                target = 2 * port + next_side
                _, chart = corners.find(points[next_side])
                flip = bool(state ^ chart)
                break
            if next_edge in visited:
                raise AssertionError('a marked literal gap never reaches a core port')
            visited.add(next_edge)
            count += 1
            _, entry_chart = corners.find(points[next_side])
            vertex, exit_chart = corners.find(points[1 - next_side])
            state ^= entry_chart ^ exit_chart
            previous = (next_edge, 1 - next_side)
        if token < target:
            gaps.append(dict(id=len(gaps), ends=[token, target],
                             old_boundary_present=bool(count), fibre_flip=flip))

    # Components of A use only the core edges; this is independent of the
    # producer's maximal-run extraction from a cyclic word.
    boundary_components = _ParityUnion(n)
    attachment_components = _ParityUnion(n)
    for points, port in edges:
        a, _ = corners.find(points[0])
        b, _ = corners.find(points[1])
        boundary_components.join(a, b)
        if port is not None:
            attachment_components.join(a, b)
    boundary_sets, attachment_sets = defaultdict(set), defaultdict(set)
    old_vertices = {corners.find(point)[0] for points, port in edges if port is None for point in points}
    attachment_vertices = defaultdict(set)
    for token, (edge, side) in tokens.items():
        vertex, _ = corners.find(edges[edge][0][side])
        boundary_sets[boundary_components.find(vertex)[0]].add(token // 2)
        root = attachment_components.find(vertex)[0]
        attachment_sets[root].add(token // 2)
        attachment_vertices[root].add(vertex)
    components = set()
    for root, ports in attachment_sets.items():
        kind = 'interval' if attachment_vertices[root] & old_vertices else 'circle'
        components.add((kind, tuple(sorted(ports))))
    return gaps, {tuple(sorted(s)) for s in boundary_sets.values()}, components


class ParallelityBoundaryWordsTests(unittest.TestCase):
    def checked(self, raw, rows, *, literal=True):
        a = normal_parallelity_boundary_words(raw, rows, record_certificate=True)
        self.assertEqual(a['status'], 'COMPLETE')
        self.assertTrue(verify_parallelity_boundary_words(raw, rows, a['certificate']))
        base = normal_cut_parallelity(raw, rows)
        skeleton = a['skeleton']
        if literal:
            gaps, boundary_sets, components = literal_interfaces(base['geometry'])
            self.assertEqual(skeleton['gaps'], gaps)
            self.assertEqual({tuple(sorted(abs(x) - 1 for x in loop['word']))
                              for loop in skeleton['boundary_loops']}, boundary_sets)
            self.assertEqual({(item['kind'], tuple(sorted(abs(x) - 1 for x in item['word'])))
                              for item in skeleton['attachment_components']}, components)
        self.assertEqual(skeleton['interval_attachments'],
                         base['summary']['attachment_euler_characteristic'])
        for item in skeleton['attachment_components']:
            matching = [p for p in base['summary']['base_profiles']
                        if item['base_anchor_port'] in p['core_ports']]
            self.assertEqual(len(matching), 1)
            self.assertTrue({abs(x) - 1 for x in item['word']} <= set(matching[0]['core_ports']))
        return a

    def test_layered_sources_zero_positive_and_large_port_chains(self):
        for t in (1, 2, 4, 8):
            raw, vector = layered_torus(t)
            for n in (0, 1, 2, 5):
                a = self.checked(raw, [[n * x for x in row] for row in vector])
                if t == 4 and n:
                    self.assertEqual(len(a['skeleton']['ports']), 15)
                    self.assertEqual(a['skeleton']['interval_attachments'], 3)
        raw, vector = layered_torus(1)
        a = normal_parallelity_boundary_words(raw, vector, max_cycles=0, record_certificate=True)
        self.assertEqual(a['stats'], {})
        self.assertIsNone(a['certificate']['gap_cover'])

    def test_one_sided_bases_and_twisted_local_transport(self):
        raw, _ = layered_torus(1)
        for n in range(1, 9):
            self.checked(raw, [[0, 0, 0, 0, 0, n, 0]])

    def test_native_bank_and_full_circle_obstructions(self):
        bank = json.loads((ROOT / 'synthesis/data/cut-complement-audit.json').read_text())['source_proofs']
        circles = 0
        for item in bank:
            literal = sum(encoded_integer(x) for row in item['coordinates'] for x in row) <= 3000
            a = self.checked(item['triangulation'], item['coordinates'], literal=literal)
            circles += a['skeleton']['circle_attachments']
        self.assertGreater(circles, 0)

    def test_relabelled_source_endpoint_and_fibre_charts(self):
        rng = random.Random(2026101231)
        for t in (2, 4):
            raw, vector = layered_torus(t)
            rows = [[3 * x for x in row] for row in vector]
            for _ in range(6):
                changed, coordinates = relabel(raw, rows, rng)
                self.checked(changed, coordinates)

    def test_binary_multiplicity_source_independence_and_sparse_partitions(self):
        raw, vector = layered_torus(2)
        n = 1 << 16384
        rows = [[n * x for x in row] for row in vector]
        a = normal_parallelity_boundary_words(raw, rows, record_certificate=True)
        p = len(a['skeleton']['ports'])
        self.assertEqual(p, 2)
        self.assertLessEqual(a['stats']['vertices']['maximum_weight_runs'], 4 * p + 1)
        self.assertLessEqual(a['stats']['gap_cover']['maximum_weight_runs'], 8 * p + 1)
        proof = json.loads(json.dumps(json_safe(a['certificate'])))
        disabled = ('fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words',
                    'fastunknot.parallelity_boundary_words._parallelity_geometry',
                    'fastunknot.parallelity_boundary_words._queries',
                    'fastunknot.parallelity_boundary_words._skeleton',
                    'fastunknot.weighted_orbits.weighted_orbit_histogram')
        with ExitStack() as stack:
            for name in disabled:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_parallelity_boundary_words(raw, json_safe(rows), proof))

    def test_hostile_source_words_tags_gaps_and_attachment_types(self):
        raw, rows = layered_torus(4)
        proof = normal_parallelity_boundary_words(raw, rows, record_certificate=True)['certificate']
        bad = []
        for key, value in (('schema', 'wrong'), ('input_sha256', '0' * 64), ('skeleton', None),
                           ('vertex_partition', None), ('gap_cover', None)):
            p = deepcopy(proof)
            p[key] = value
            bad.append(p)
        for field in ('fibre_flip', 'old_boundary_present'):
            p = deepcopy(proof)
            p['skeleton']['gaps'][0][field] ^= True
            bad.append(p)
        p = deepcopy(proof)
        p['skeleton']['boundary_loops'][0]['word'][0] *= -1
        bad.append(p)
        p = deepcopy(proof)
        p['skeleton']['attachment_components'][0]['kind'] = 'circle'
        bad.append(p)
        p = deepcopy(proof)
        p['skeleton']['ports'][0]['core_handle'] += 1
        bad.append(p)
        p = deepcopy(proof)
        p['skeleton']['ports'][0]['id'] = False
        bad.append(p)
        p = deepcopy(proof)
        p['gap_cover']['histogram'][-1]['weight'][0] += 1
        bad.append(p)
        for p in bad:
            self.assertFalse(verify_parallelity_boundary_words(raw, rows, p))
        changed = [[2 * x for x in row] for row in rows]
        self.assertFalse(verify_parallelity_boundary_words(raw, changed, proof))

    def test_shared_caps_and_cooperative_cancellation(self):
        raw, rows = layered_torus(4)
        a = normal_parallelity_boundary_words(raw, rows, record_certificate=True)
        cycles = sum(s['orbit_cycles'] for s in a['stats'].values())
        for cap in (0, cycles - 1):
            b = normal_parallelity_boundary_words(raw, rows, max_cycles=cap, record_certificate=True)
            self.assertEqual(b['status'], 'INCONCLUSIVE')
            self.assertNotIn('skeleton', b)
            self.assertNotIn('certificate', b)
        self.assertEqual(normal_parallelity_boundary_words(raw, rows, max_cycles=cycles)['skeleton'],
                         a['skeleton'])
        proof = a['certificate']
        events = sum(len(proof[field]['orbit_proof']['operations'])
                     for field in ('vertex_partition', 'gap_cover'))
        self.assertFalse(verify_parallelity_boundary_words(raw, rows, proof, max_operations=events - 1))
        self.assertTrue(verify_parallelity_boundary_words(raw, rows, proof, max_operations=events))

        class Cancel:
            def __bool__(self):
                return False

            def __call__(self):
                raise ValueError('cancelled')

        with self.assertRaisesRegex(ValueError, 'cancelled'):
            normal_parallelity_boundary_words(raw, rows, check=Cancel())
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            verify_parallelity_boundary_words(raw, rows, proof, check=Cancel())

    def test_sparse_token_weighted_orbits_have_uniform_partition_bound(self):
        rng = random.Random(2026101241)
        for bits in (8, 32, 512, 16384):
            size = (1 << bits) + 31
            period = 37
            points = [rng.randrange(size) for _ in range(12)]
            weights = [(point, point + 1, [1 << i]) for i, point in enumerate(points)]
            pairs = [IntervalPairing(0, size - period - 1, period, size - 1)]
            a = weighted_orbit_histogram(size, pairs, weights, dimension=1,
                                         periodic_rule='aht', record_certificate=True)
            residues = defaultdict(int)
            for i, point in enumerate(points):
                residues[point % period] |= 1 << i
            expected = {value: 1 for value in residues.values()}
            expected[0] = period - len(residues)
            self.assertEqual({r['weight'][0]: r['orbits'] for r in a['histogram']}, expected)
            self.assertLessEqual(a['stats']['maximum_weight_runs'], 2 * len(points) + 1)
            self.assertTrue(verify_weighted_orbit_certificate(size, pairs, weights,
                                                             a['certificate'], dimension=1))


if __name__ == '__main__':
    unittest.main()
