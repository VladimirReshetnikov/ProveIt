"""Marked compressed normal-boundary orders against literal edge occurrences."""

from collections import Counter
import copy
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.marked_boundary import marked_boundary_order, normal_marked_boundary_order
from fastunknot.marked_boundary_verify import (
    verify_marked_boundary_certificate, verify_normal_marked_boundary_certificate,
)
from fastunknot.normal_surface_geometry import NormalOrbitError, normal_arc_pairings
from normal_orbit_research.fixtures import (
    boundary_cap, interior_vertex_torus, layered_torus, regina_surface, regina_triangulation,
)


def literal_order(size, pairs, marks, direction=None):
    """Expand a small multigraph, retaining both incidences of every edge."""
    adjacency = [[] for _ in range(size)]
    endpoint = {}
    for row, pair in enumerate(pairs):
        for source in range(pair.a, pair.b + 1):
            target = pair.image(source)
            for point, side in ((source, 0), (target, 1)):
                key = (row, source, side)
                adjacency[point].append(key)
                endpoint[key] = point
    assert all(len(ends) == 2 for ends in adjacency)
    by_point = {point: index for index, point in enumerate(marks)}
    port_keys = sorted((by_point[point], *key) for point in marks for key in adjacency[point])
    ports = [dict(zip(('mark', 'pairing', 'source', 'side'), key)) for key in port_keys]
    key_to_port = {tuple(key[1:]): index for index, key in enumerate(port_keys)}

    def step(key):
        row, source, side = key
        arrival = (row, source, 1 - side)
        vertex = endpoint[arrival]
        alternatives = adjacency[vertex]
        outgoing = alternatives[0] if alternatives[1] == arrival else alternatives[1]
        return vertex, arrival, outgoing

    connections = {}
    for key, port in key_to_port.items():
        current, length = key, 0
        while True:
            point, arrival, current = step(current)
            if point in by_point:
                ends = tuple(sorted((port, key_to_port[arrival])))
                connections[ends] = length
                break
            length += 1
            assert length <= size

    def walk(key):
        current = key
        order, departures, lengths = [], [], []
        gap = 0
        while True:
            point = endpoint[current]
            if point in by_point:
                order.append(by_point[point])
                departures.append(key_to_port[current])
            next_point, arrival, following = step(current)
            if next_point in by_point:
                lengths.append(gap)
                gap = 0
            else:
                gap += 1
            current = following
            if current == key:
                break
        return dict(marks=order, departures=departures, gaps=lengths,
                    vertices=len(order) + sum(lengths))

    remaining, cycles, unmarked = set(range(size)), [], Counter()
    while remaining:
        first = min(remaining)
        component, current = {first}, adjacency[first][0]
        initial = current
        while True:
            vertex, _, current = step(current)
            component.add(vertex)
            if current == initial:
                break
        remaining.difference_update(component)
        present = sorted(by_point[point] for point in component if point in by_point)
        if not present:
            unmarked[len(component)] += 1
            continue
        point = marks[present[0]]
        candidates = [walk(key) for key in adjacency[point]]
        cycle = min(candidates, key=lambda item: (item['marks'], item['departures']))
        if direction is not None and endpoint[tuple(direction)] in component:
            cycle = walk(tuple(direction))
        cycles.append(cycle)
    return dict(ports=ports, connections=[dict(ports=list(ends), unmarked_vertices=length)
                for ends, length in sorted(connections.items())],
                cycles=sorted(cycles, key=lambda item: min(item['marks'])),
                unmarked_cycles=[dict(vertices=length, components=count)
                                 for length, count in sorted(unmarked.items())],
                component_count=len(cycles) + sum(unmarked.values()))


def interval_exchange(randomizer, size):
    """A random signed interval permutation is a compressed degree-two graph."""
    cuts = sorted(set([0, size] + [randomizer.randrange(size + 1)
                                 for _ in range(randomizer.randrange(1, 12))]))
    blocks = list(zip(cuts, cuts[1:]))
    image_order = list(range(len(blocks)))
    randomizer.shuffle(image_order)
    images, offset = {}, 0
    for index in image_order:
        width = blocks[index][1] - blocks[index][0]
        images[index] = (offset, offset + width)
        offset += width
    return [IntervalPairing(left, right - 1, images[index][0], images[index][1] - 1,
                            bool(randomizer.randrange(2)))
            for index, (left, right) in enumerate(blocks)]


class MarkedBoundaryTests(unittest.TestCase):
    def checked(self, size, pairs, marks, **options):
        answer = marked_boundary_order(size, pairs, marks, record_certificate=True, **options)
        self.assertEqual(answer['status'], 'COMPLETE')
        expected = literal_order(size, pairs, marks, options.get('start_half_edge'))
        self.assertEqual({key: answer[key] for key in expected}, expected)
        self.assertTrue(verify_marked_boundary_certificate(
            size, pairs, marks, answer['certificate'],
            start_half_edge=options.get('start_half_edge'),
            weight_encoding=options.get('weight_encoding', 'moments')))
        self.assertLessEqual(answer['stats']['residual_pairings'], len(pairs) + 2 * len(marks))
        self.assertEqual(sum(row['vertices'] for row in answer['cycles'])
                         + sum(row['vertices'] * row['components']
                               for row in answer['unmarked_cycles']), size)
        return answer

    def test_seeded_signed_interval_permutations(self):
        rng = random.Random(904817)
        for case in range(500):
            size = rng.randrange(1, 61)
            pairs = interval_exchange(rng, size)
            marks = rng.sample(range(size), rng.randrange(size + 1))
            self.checked(size, pairs, marks, periodic_rule='aht' if case % 2 else 'fine_wilf',
                         weight_encoding='one_hot' if case % 3 == 0 else 'moments')

    def test_moment_and_one_hot_modes_have_identical_occurrence_orders(self):
        rng = random.Random(138029)
        for _ in range(100):
            size = rng.randrange(1, 51)
            pairs = interval_exchange(rng, size)
            marks = rng.sample(range(size), rng.randrange(size + 1))
            moments = self.checked(size, pairs, marks)
            basis = self.checked(size, pairs, marks, weight_encoding='one_hot')
            self.assertEqual(moments['certificate']['solution'], basis['certificate']['solution'])
            self.assertEqual(moments['stats']['weight_dimension'], 4)
            self.assertEqual(basis['stats']['weight_dimension'], 2 * len(marks) + 1)
            self.assertFalse(verify_marked_boundary_certificate(
                size, pairs, marks, moments['certificate'], weight_encoding='one_hot'))
            self.assertFalse(verify_marked_boundary_certificate(
                size, pairs, marks, basis['certificate'], weight_encoding='moments'))

    def test_empty_all_marked_loops_and_reflection_parallel_edges(self):
        self.checked(0, [], [])
        self.checked(9, [IntervalPairing(0, 8, 0, 8)], [])
        self.checked(9, [IntervalPairing(0, 8, 0, 8)], [8, 0, 4])
        self.checked(7, [IntervalPairing(0, 6, 0, 6, True)], list(range(7)))
        self.checked(8, [IntervalPairing(0, 7, 0, 7, True)], [0, 7, 3])
        self.checked(2, [IntervalPairing(0, 0, 1, 1), IntervalPairing(0, 0, 1, 1)], [1, 0])

    def test_adjacent_marks_singleton_residual_paths_and_direction(self):
        pairs = [IntervalPairing(0, 8, 1, 9), IntervalPairing(0, 0, 9, 9)]
        marks = [3, 0, 2, 7, 8, 9]
        answer = self.checked(10, pairs, marks)
        for port in answer['ports']:
            direction = [port[key] for key in ('pairing', 'source', 'side')]
            directed = self.checked(10, pairs, marks, start_half_edge=direction)
            cycle = directed['cycles'][0]
            self.assertEqual(cycle['marks'][0], port['mark'])
            self.assertEqual(directed['ports'][cycle['departures'][0]], port)

    def test_native_layered_and_capped_normal_boundaries(self):
        rng = random.Random(47183)
        for tetrahedra in range(1, 9):
            raw, coordinates = layered_torus(tetrahedra)
            for caps in range(3):
                if caps:
                    raw, coordinates = boundary_cap(raw, coordinates)
                for scale in (1, 2, 3):
                    scaled = [[scale * value for value in row] for row in coordinates]
                    size, pairs = normal_arc_pairings(raw, scaled, boundary=True)
                    marks = rng.sample(range(size), min(size, 11))
                    answer = self.checked(size, pairs, marks)
                    native = normal_marked_boundary_order(raw, scaled, marks, record_certificate=True)
                    self.assertEqual(answer['cycles'], native['cycles'])
                    self.assertEqual(answer['component_count'], scale)
                    self.assertTrue(verify_normal_marked_boundary_certificate(
                        raw, scaled, marks, native['certificate']))

    def test_native_mobius_sphere_and_vertex_boundary_mixtures(self):
        rng = random.Random(22147)
        raw, basis = interior_vertex_torus()
        for sphere in (0, 1):
            for disk in range(3):
                for mobius in range(5):
                    rows = [[sphere * basis['sphere'][t][j]
                             + disk * basis['boundary_disk'][t][j]
                             + mobius * basis['mobius'][t][j] for j in range(7)]
                            for t in range(4)]
                    size, pairs = normal_arc_pairings(raw, rows, boundary=True)
                    marks = rng.sample(range(size), min(size, 9))
                    answer = self.checked(size, pairs, marks)
                    # Two copies of a one-sided Mobius band form an annulus:
                    # component count changes, but both boundary curves remain.
                    self.assertEqual(answer['component_count'], disk + mobius)

    def test_huge_native_binary_coordinates_and_hex_transport(self):
        raw, rows = layered_torus(24)
        scale = 1 << 20000
        coordinates = [[hex(scale * value) for value in row] for row in rows]
        size, pairs = normal_arc_pairings(raw, coordinates, boundary=True)
        marks = [0, scale - 1, scale, size - 1]
        answer = normal_marked_boundary_order(raw, coordinates, marks, record_certificate=True)
        self.assertEqual(answer['status'], 'COMPLETE')
        self.assertEqual(answer['component_count'], scale)
        self.assertLessEqual(answer['stats']['residual_pairings'], len(pairs) + 2 * len(marks))
        self.assertTrue(verify_marked_boundary_certificate(
            hex(size), pairs, [hex(point) for point in marks], json_safe(answer['certificate'])))
        self.assertTrue(verify_normal_marked_boundary_certificate(
            raw, coordinates, [hex(point) for point in marks], json_safe(answer['certificate'])))

    def test_optional_regina_native_boundary_count(self):
        try:
            import regina  # noqa: F401 -- optional independent topology oracle
        except ImportError:
            self.skipTest('Regina is an optional independent check')
        for tetrahedra in range(1, 7):
            raw, rows = layered_torus(tetrahedra)
            for _ in range(tetrahedra % 3):
                raw, rows = boundary_cap(raw, rows)
            triangulation = regina_triangulation(raw)
            for scale in (1, 2, 3):
                coordinates = [[scale * value for value in row] for row in rows]
                size, pairs = normal_arc_pairings(raw, coordinates, boundary=True)
                marks = [0, size - 1] if size > 1 else [0]
                answer = marked_boundary_order(size, pairs, marks)
                surface = regina_surface(triangulation, coordinates)
                self.assertEqual(answer['component_count'], surface.countBoundaries())

    def test_huge_unmarked_length_and_multiplicity(self):
        size = 1 << 17000
        cycle = [IntervalPairing(0, size - 2, 1, size - 1), IntervalPairing(0, 0, size - 1, size - 1)]
        answer = marked_boundary_order(size, cycle, [size // 3, size - 2], record_certificate=True)
        self.assertEqual(answer['cycles'][0]['vertices'], size)
        self.assertTrue(verify_marked_boundary_certificate(size, cycle,
                        [size // 3, size - 2], json_safe(answer['certificate'])))
        loops = [IntervalPairing(0, size - 1, 0, size - 1)]
        answer = marked_boundary_order(size, loops, [0], record_certificate=True)
        self.assertEqual(answer['unmarked_cycles'], [dict(vertices=1, components=size - 1)])
        self.assertTrue(verify_marked_boundary_certificate(size, loops, [0],
                                                         json_safe(answer['certificate'])))

    def test_source_and_output_mutations_rejected(self):
        pairs = [IntervalPairing(0, 12, 1, 13), IntervalPairing(0, 0, 13, 13)]
        marks = [0, 5, 13]
        answer = marked_boundary_order(14, pairs, marks, record_certificate=True)
        proof = answer['certificate']
        mutations = []
        for field, value in [('schema', 'wrong'), ('size', 15), ('marks', [0, 6, 13]),
                             ('start_half_edge', [0, 0, 0]), ('pairings', []),
                             ('weight_encoding', 'one_hot')]:
            other = copy.deepcopy(proof)
            other[field] = value
            mutations.append(other)
        for field in ('connections', 'cycles', 'ports'):
            other = copy.deepcopy(proof)
            other['solution'][field].pop()
            mutations.append(other)
        other = copy.deepcopy(proof)
        other['solution']['cycles'][0]['marks'].reverse()
        mutations.append(other)
        other = copy.deepcopy(proof)
        other['solution']['connections'][0]['unmarked_vertices'] += 1
        mutations.append(other)
        other = copy.deepcopy(proof)
        other['weighted_proof']['histogram'][0]['weight'][-1] += 1
        mutations.append(other)
        other = copy.deepcopy(proof)
        other['weighted_proof']['orbit_proof']['orbit_count'] += 1
        mutations.append(other)
        other = copy.deepcopy(proof)
        other['solution']['component_count'] = True
        mutations.append(other)
        for forged in mutations:
            self.assertFalse(verify_marked_boundary_certificate(14, pairs, marks, forged))
        self.assertFalse(verify_marked_boundary_certificate(14, pairs[::-1], marks, proof))
        self.assertFalse(verify_marked_boundary_certificate(14, pairs, marks[::-1], proof))
        self.assertFalse(verify_marked_boundary_certificate(14, pairs, marks, proof,
                                                         start_half_edge=[0, 0, 0]))
        with patch('fastunknot.marked_boundary.marked_boundary_order',
                   side_effect=AssertionError('producer must not be called')):
            self.assertTrue(verify_marked_boundary_certificate(14, pairs, marks, proof))

    def test_degree_guard_and_mark_validation(self):
        cases = [(1, None, []), (1, [], []), (3, [IntervalPairing(0, 1, 1, 2)], []),
                 (2, [IntervalPairing(0, 1, 0, 1)] * 2, [0]),
                 (1, [IntervalPairing(0, 0, 0, 0)], [0, 0]),
                 (1, [IntervalPairing(0, 0, 0, 0)], [1]),
                 (1, [IntervalPairing(0, 0, 0, 0)], [True]),
                 (True, [], []), (-1, [], [])]
        for size, pairs, marks in cases:
            with self.assertRaises(ValueError):
                marked_boundary_order(size, pairs, marks)
            self.assertFalse(verify_marked_boundary_certificate(size, pairs, marks, {}))
        for selected in ([1, 0, 0], [0, 1, 0], [0, 0, 2], [0, 0], [True, 0, 0]):
            with self.assertRaises(ValueError):
                marked_boundary_order(1, [IntervalPairing(0, 0, 0, 0)], [0],
                                      start_half_edge=selected)
        with self.assertRaises(ValueError):
            marked_boundary_order(0, [], [], record_certificate=1)
        with self.assertRaises(ValueError):
            marked_boundary_order(0, [], [], weight_encoding='arbitrary_fingerprint')

    def test_budget_and_cooperative_cancellation(self):
        pairs = [IntervalPairing(0, 12, 1, 13), IntervalPairing(0, 0, 13, 13)]
        answer = marked_boundary_order(14, pairs, [0, 5], max_cycles=0, record_certificate=True)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', answer)
        self.assertNotIn('cycles', answer)
        proof = marked_boundary_order(14, pairs, [0, 5], record_certificate=True)['certificate']

        class Cancelled(Exception):
            pass

        def stop():
            raise Cancelled('cooperative cancellation')

        with self.assertRaises(Cancelled):
            marked_boundary_order(14, pairs, [0, 5], check=stop)
        with self.assertRaises(Cancelled):
            verify_marked_boundary_certificate(14, pairs, [0, 5], proof, check=stop)

    def test_native_geometry_callback_error_keeps_its_identity(self):
        raw, coordinates = layered_torus(2)
        geometry_polls = 0

        def count_geometry():
            nonlocal geometry_polls
            geometry_polls += 1

        size, pairs = normal_arc_pairings(raw, coordinates, boundary=True, check=count_geometry)
        marks = [0, 3, size - 1]
        proof = marked_boundary_order(size, pairs, marks, record_certificate=True)['certificate']
        self.assertGreater(geometry_polls, 1)
        for target in (1, geometry_polls, geometry_polls + 1):
            with self.subTest(callback_poll=target):
                calls = 0
                error = NormalOrbitError('external geometry callback cancellation')

                def cancel():
                    nonlocal calls
                    calls += 1
                    if calls == target:
                        raise error

                with self.assertRaises(NormalOrbitError) as caught:
                    verify_normal_marked_boundary_certificate(
                        raw, coordinates, marks, proof, check=cancel)
                self.assertIs(caught.exception, error)
        self.assertFalse(verify_normal_marked_boundary_certificate(
            {}, coordinates, marks, proof))


if __name__ == '__main__':
    unittest.main()
