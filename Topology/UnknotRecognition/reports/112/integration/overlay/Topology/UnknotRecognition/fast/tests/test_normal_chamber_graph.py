"""Native chamber graphs against explicitly glued small normal cut models."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import encoded_integer
from fastunknot.normal_chamber_graph import normal_chamber_graph
from fastunknot.normal_chamber_graph_verify import verify_normal_chamber_graph
from fastunknot.normal_cut_cells_verify import _reference_cells
from fastunknot.normal_cut_complement_verify import _reference_chambers
from fastunknot.normal_surface_geometry import _coordinates, _prepare, _quad
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


class DSU:
    def __init__(self, count):
        self.parent = list(range(count))

    def root(self, vertex):
        while self.parent[vertex] != vertex:
            vertex = self.parent[vertex]
        return vertex

    def join(self, a, b):
        a, b = self.root(a), self.root(b)
        if a != b:
            self.parent[b] = a


def literal_disc_components(prepared, rows):
    """Glue individual discs by face-arc ranks, independent of edge orbits."""
    discs = [(t, c, r) for t, row in enumerate(rows)
             for c, count in enumerate(row) for r in range(count)]
    if len(discs) > 20000:
        raise ValueError('literal reference is deliberately bounded')
    number = {disc: i for i, disc in enumerate(discs)}
    dsu = DSU(len(discs))

    def stack(t, face, vertex):
        row = rows[t]
        col = 4 + _quad(face, vertex)
        ranks = range(row[col]) if vertex in (0, col - 3) else range(row[col] - 1, -1, -1)
        return ([(t, vertex, r) for r in range(row[vertex])]
                + [(t, col, r) for r in ranks])

    for t, f, u, g, permutation in prepared['pairs']:
        for vertex in range(4):
            if vertex == f:
                continue
            a, b = stack(t, f, vertex), stack(u, g, permutation[vertex])
            if len(a) != len(b):
                raise AssertionError('literal face arcs do not match')
            for x, y in zip(a, b):
                dsu.join(number[x], number[y])
    groups = {}
    for i, disc in enumerate(discs):
        groups.setdefault(dsu.root(i), []).append(disc)
    return list(groups.values())


def literal_chamber_model(prepared, analysed, groups):
    """Expand actual cut cells and all omitted-surface gluings for an oracle."""
    cells = _reference_cells(prepared, analysed, lambda: None)
    if cells['chamber_points'] > 20000:
        raise ValueError('literal cut reference is deliberately bounded')
    dsu = DSU(cells['chamber_points'])
    incidence = {}
    for item in cells['face_incidence']:
        for face in range(item['face_start'], item['face_stop']):
            slope, offset = item['chamber']
            incidence.setdefault(face, []).append(slope * face + offset)
    for family in cells['faces']:
        if family['kind'] == 'horizontal' or family['boundary']:
            continue
        for face in range(family['start'], family['stop']):
            endpoints = incidence[face]
            if len(endpoints) != 2:
                raise AssertionError('interior original face has wrong valence')
            dsu.join(*endpoints)
    horizontal = {(f['tetrahedron'], f['column'], f['side']): f['start']
                  for f in cells['faces'] if f['kind'] == 'horizontal'}
    gates = []
    for group in groups:
        group_gates = []
        for t, c, r in group:
            group_gates.append(tuple(incidence[horizontal[t, c, side] + r][0]
                                     for side in (0, 1)))
        gates.append(group_gates)
    return dsu, gates


def labelled_representatives(groups):
    return [dict(tetrahedron=g[0][0], column=g[0][1], rank=g[0][2]) for g in groups]


def check_literal_graph(test, raw, rows, *, exhaustive_limit=8):
    prepared = _prepare(raw, lambda: None)
    analysed = _coordinates(prepared, rows, lambda: None)
    groups = literal_disc_components(prepared, analysed['rows'])
    reps = labelled_representatives(groups)
    output = normal_chamber_graph(raw, rows, reps, record_certificate=True)
    doubled = literal_disc_components(prepared, [[2 * x for x in row] for row in analysed['rows']])
    if len(doubled) != 2 * len(groups):
        test.assertEqual(output['status'], 'INCONCLUSIVE')
        test.assertEqual(output['reason'], 'one_sided_surface_component')
        test.assertNotIn('certificate', output)
        return output, 0
    test.assertEqual(output['status'], 'COMPLETE')
    test.assertTrue(verify_normal_chamber_graph(raw, rows, output['certificate']))
    base, gates = literal_chamber_model(prepared, analysed, groups)
    test.assertEqual(output['graph']['vertices'], len({base.root(v) for v in base.parent}))
    k = len(groups)
    choices = range(1 << k) if k <= exhaustive_limit else [0, (1 << k) - 1]
    checked = 0
    for chosen in choices:
        literal = deepcopy(base)
        graph = DSU(output['graph']['vertices'])
        for i, endpoints in enumerate(output['graph']['edges']):
            if chosen & (1 << i):
                continue
            graph.join(*endpoints)
            for pair in gates[i]:
                literal.join(*pair)
        expected = len({literal.root(v) for v in literal.parent})
        actual = len({graph.root(v) for v in graph.parent})
        test.assertEqual(actual, expected)
        # Regenerate a separate cut from exactly the selected component
        # coordinates, then expand its independent chamber relation.
        selected_rows = [[0] * 7 for _ in rows]
        for i, group in enumerate(groups):
            if chosen & (1 << i):
                for t, c, _ in group:
                    selected_rows[t][c] += 1
        _coordinates(prepared, selected_rows, lambda: None)
        size, pairings = _reference_chambers(prepared, selected_rows, lambda: None)
        regenerated = DSU(size)
        for a, b, c, d, sign in pairings:
            for rank in range(b - a + 1):
                regenerated.join(a + rank, c + rank if sign == 1 else d - rank)
        test.assertEqual(actual, len({regenerated.root(v) for v in regenerated.parent}))
        checked += 1
    return output, checked


class NormalChamberGraphTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bank = json.loads((Path(__file__).parents[1]
            / 'marked_parallelity_research/corpus.json').read_text())['cases']
        cls.base = cls.bank[0]
        cls.raw, cls.rows = cls.base['triangulation'], cls.base['coordinates']

    def test_native_small_corpus_and_all_regluing_subsets(self):
        checks, positives, one_sided = 0, 0, 0
        for case in self.bank:
            rows = [[encoded_integer(x) for x in row] for row in case['coordinates']]
            if sum(map(sum, rows)) > 500:
                continue
            output, number = check_literal_graph(self, case['triangulation'], rows)
            checks += number
            positives += output['status'] == 'COMPLETE'
            one_sided += output.get('reason') == 'one_sided_surface_component'
        self.assertGreater(positives, 40)
        self.assertGreater(one_sided, 0)
        self.assertGreater(checks, 100)

    def test_parallel_components_are_labelled_without_coordinate_division(self):
        for scale in (2, 3, 7):
            rows = [[scale * x for x in row] for row in self.rows]
            reps = [dict(tetrahedron=0, column=2, rank=i) for i in range(scale)]
            result = normal_chamber_graph(self.raw, rows, reps, record_certificate=True)
            self.assertEqual(result['status'], 'COMPLETE')
            self.assertEqual(result['surface_components'], scale)
            self.assertEqual(result['graph']['vertices'], scale + 1)
            self.assertTrue(verify_normal_chamber_graph(self.raw, rows, result['certificate']))
            refused = normal_chamber_graph(self.raw, rows)
            self.assertEqual(refused['reason'], 'representatives_do_not_label_components')
            self.assertNotIn('graph', refused)

    def test_actual_one_sided_surface_and_its_two_sided_double(self):
        rows = [[0, 0, 0, 0, 0, 1, 0]]
        result = normal_chamber_graph(self.raw, rows)
        self.assertEqual(result['reason'], 'one_sided_surface_component')
        result = normal_chamber_graph(self.raw, [[2 * x for x in rows[0]]], record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertTrue(verify_normal_chamber_graph(self.raw, [[2 * x for x in rows[0]]], result['certificate']))

    def test_same_component_marked_twice_is_rejected(self):
        reps = [dict(tetrahedron=0, column=c, rank=0) for c in (2, 3)]
        result = normal_chamber_graph(self.raw, self.rows, reps, record_certificate=True)
        self.assertEqual(result['reason'], 'representatives_do_not_label_components')
        self.assertNotIn('certificate', result)

    def test_empty_surface_and_invalid_representatives(self):
        rows = [[0] * 7 for _ in self.rows]
        result = normal_chamber_graph(self.raw, rows, record_certificate=True)
        self.assertEqual(result['graph'], dict(vertices=1, edges=[], chamber_masks=[0], cycle_rank=0))
        self.assertTrue(verify_normal_chamber_graph(self.raw, rows, result['certificate']))
        for reps in ({}, [dict(tetrahedron=False, column=2, rank=0)],
                     [dict(tetrahedron=0, column=2, rank=1)], [dict(tetrahedron=0, column=7, rank=0)]):
            with self.assertRaises(ValueError):
                normal_chamber_graph(self.raw, self.rows, reps)

    def test_source_mutations_producer_disabled_and_hexadecimal_fields(self):
        result = normal_chamber_graph(self.raw, self.rows, record_certificate=True)
        proof = result['certificate']
        changes = [
            lambda p: p.update(input_sha256='0' * 64),
            lambda p: p['representatives'][0].update(rank=True),
            lambda p: p['markers'][0].update(surface_point=999),
            lambda p: p['markers'][0].update(positive_chamber=999),
            lambda p: p['graph'].update(cycle_rank=999),
            lambda p: p['graph']['edges'][0].__setitem__(1, 0),
            lambda p: p['proofs']['orientation_double'].update(orbit_count=1),
            lambda p: p['proofs']['surface_labels']['histogram'][0].update(weight=[2]),
            lambda p: p['proofs']['chamber_sides']['histogram'][0].update(orbits=2),
            lambda p: p['proofs'].pop('orientation_double'),
        ]
        for change in changes:
            malformed = deepcopy(proof)
            change(malformed)
            self.assertFalse(verify_normal_chamber_graph(self.raw, self.rows, malformed))
        encoded = deepcopy(proof)
        encoded['representatives'][0]['tetrahedron'] = '0x0'
        encoded['markers'][0]['label'] = '+0X0'
        with ExitStack() as stack:
            for name in ('fastunknot.normal_chamber_graph.normal_chamber_graph',
                         'fastunknot.normal_chamber_graph._markers',
                         'fastunknot.normal_chamber_graph._graph',
                         'fastunknot.normal_cut_complement._chamber_system',
                         'fastunknot.weighted_orbits.weighted_orbit_histogram',
                         'fastunknot.interval_orbits.count_orbits'):
                stack.enter_context(patch(name, side_effect=AssertionError('producer called')))
            self.assertTrue(verify_normal_chamber_graph(self.raw, self.rows, encoded))

    def test_shared_allowance_and_callback_propagation(self):
        result = normal_chamber_graph(self.raw, self.rows, record_certificate=True)
        used = result['stats']['orbit_cycles']
        self.assertGreater(used, 0)
        self.assertEqual(normal_chamber_graph(self.raw, self.rows, max_cycles=used)['status'], 'COMPLETE')
        for cap in (0, used - 1):
            incomplete = normal_chamber_graph(self.raw, self.rows, max_cycles=cap, record_certificate=True)
            self.assertEqual(incomplete['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', incomplete)
            self.assertNotIn('graph', incomplete)
        self.assertFalse(verify_normal_chamber_graph(self.raw, self.rows, result['certificate'], max_operations=0))

        def stop():
            raise RuntimeError('cancelled')

        with self.assertRaises(RuntimeError):
            normal_chamber_graph(self.raw, self.rows, check=stop)
        with self.assertRaises(RuntimeError):
            verify_normal_chamber_graph(self.raw, self.rows, result['certificate'], check=stop)

    def test_binary_component_explosion_is_not_expanded(self):
        case = next(c for c in self.bank if c['id'] == 'binary/1/16384')
        result = normal_chamber_graph(case['triangulation'], case['coordinates'], record_certificate=True)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'representatives_do_not_label_components')
        self.assertLess(result['stats']['orbit_cycles'], 100)
        self.assertNotIn('certificate', result)
        self.assertNotIn('graph', result)

    def test_relabelled_multi_component_source(self):
        rng = random.Random(209119)
        rows = [[3 * x for x in row] for row in self.rows]
        for _ in range(10):
            raw, moved = relabel(self.raw, rows, rng)
            check_literal_graph(self, raw, moved)

    def test_quad_ranks_label_order_and_local_coorientation_reversal(self):
        raw, base = layered_torus(1)
        rows = [[3 * x for x in base[0]]]
        reps = [dict(tetrahedron=0, column=0, rank=i) for i in range(3)]
        result = normal_chamber_graph(raw, rows, reps, record_certificate=True)

        def renamed(masks, permutation):
            values = [sum(1 << permutation[b] for b in range(6) if mask & (1 << b))
                      for mask in masks]
            return sorted(values, key=lambda v: (v & -v).bit_length())

        reversed_labels = normal_chamber_graph(raw, rows, reps[::-1], record_certificate=True)
        self.assertEqual(reversed_labels['graph']['chamber_masks'],
                         renamed(result['graph']['chamber_masks'], [4, 5, 2, 3, 0, 1]))
        # On this actual component, triangle (0,1,2) chooses the opposite
        # local coorientation from triangle (0,0,0); other labels stay fixed.
        flipped = [dict(tetrahedron=0, column=1, rank=2), *reps[1:]]
        changed = normal_chamber_graph(raw, rows, flipped, record_certificate=True)
        self.assertEqual(changed['graph']['chamber_masks'],
                         renamed(result['graph']['chamber_masks'], [1, 0, 2, 3, 4, 5]))
        quads = [dict(tetrahedron=0, column=6, rank=i) for i in range(3)]
        changed_quad = normal_chamber_graph(raw, rows, quads, record_certificate=True)
        self.assertEqual(changed_quad['graph'], result['graph'])
        for output in (reversed_labels, changed, changed_quad):
            self.assertTrue(verify_normal_chamber_graph(raw, rows, output['certificate']))

    def test_connected_exponential_coordinate_meridian(self):
        raw, rows = layered_torus(128)
        representative = [dict(tetrahedron=0, column=6, rank=rows[0][6] - 1)]
        output = normal_chamber_graph(raw, rows, representative, record_certificate=True)
        self.assertEqual(output['status'], 'COMPLETE')
        self.assertEqual(output['graph'], dict(vertices=1, edges=[[0, 0]],
                                              chamber_masks=[3], cycle_rank=1))
        self.assertGreater(output['normal_disks'], 10 ** 27)
        self.assertEqual(output['surface_components'], 1)
        self.assertTrue(verify_normal_chamber_graph(raw, rows, output['certificate']))


if __name__ == '__main__':
    unittest.main()
