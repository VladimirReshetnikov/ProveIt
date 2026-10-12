"""Source reconstruction, hostile replay, and exhaustive weighted optimality."""

from contextlib import ExitStack
from copy import deepcopy
from itertools import combinations
import json
import random
import unittest
from unittest.mock import patch

from core_dual_fixtures import (interior_loop_torus, nested_interior_torus,
                                relabel, vertex_link_coordinates)
from fastunknot.core_dual_forest import core_dual_forest, dual_forest_plan
from fastunknot.core_dual_forest_verify import replay_core_dual_forest
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from normal_orbit_research.fixtures import interior_vertex_torus, layered_torus


def source(raw, coordinates):
    result = normal_cut_parallelity(raw, coordinates, record_certificate=True)
    if result['status'] != 'COMPLETE':
        raise AssertionError(result)
    return result


class CoreDualForestTests(unittest.TestCase):
    def test_source_vertex_links_and_ports_preserved(self):
        raw, basis = interior_vertex_torus()
        vectors = [dict(name='empty', rows=[[0] * 7 for _ in basis['sphere']])]
        vectors += [dict(name=name, rows=rows) for name, rows in basis.items()]
        for sample in vectors:
            geometry = source(raw, sample['rows'])['geometry']
            before = deepcopy(geometry)
            for strategy in ('bfs', 'max_weight'):
                result = core_dual_forest(geometry, strategy=strategy)
                self.assertEqual(result['status'], 'COMPLETE')
                self.assertEqual(replay_core_dual_forest(
                    geometry, result['certificate']), result['core'])
                self.assertEqual(result['core']['handles3'], [])
                self.assertEqual(result['core']['handles0'], geometry['core']['handles0'])
                self.assertEqual(result['core']['handles1'], geometry['core']['handles1'])
                for new, old in enumerate(result['certificate']['surviving_two_handles']):
                    self.assertEqual(result['core']['handles2'][new],
                                     dict(geometry['core']['handles2'][old], id=new))
                old_counts = [len(geometry['core'][f'handles{i}']) for i in range(4)]
                new_counts = [len(result['core'][f'handles{i}']) for i in range(4)]
                self.assertEqual(sum((-1) ** i * n for i, n in enumerate(old_counts)),
                                 sum((-1) ** i * n for i, n in enumerate(new_counts)))
            self.assertEqual(geometry, before)

    def test_all_three_handles_cancel_in_nested_source(self):
        raw = nested_interior_torus(4)
        geometry = source(raw, vertex_link_coordinates(raw))['geometry']
        count = len(geometry['core']['handles3'])
        self.assertEqual(count, 5)
        for strategy in ('bfs', 'max_weight'):
            result = core_dual_forest(geometry, strategy=strategy)
            self.assertEqual(len(result['certificate']['cancellations']), count)
            self.assertEqual(replay_core_dual_forest(geometry, result['certificate']),
                             result['core'])
            proof = result['certificate']
            self.assertTrue(any(-1 not in proof['source_sides'][edge]
                                for _, edge in proof['cancellations']))
            reversed_proof = deepcopy(proof)
            reversed_proof['cancellations'].reverse()
            self.assertIsNone(replay_core_dual_forest(geometry, reversed_proof))

    def test_source_loop_has_two_incidences_and_positive_weight_splits_it(self):
        raw = interior_loop_torus()
        zero = source(raw, vertex_link_coordinates(raw))['geometry']
        empty = core_dual_forest(zero)
        loops = [i for i, side in enumerate(empty['certificate']['source_sides'])
                 if side == [0, 0]]
        self.assertTrue(loops)
        for edge in loops:
            self.assertNotIn(edge, [e for _, e in empty['certificate']['cancellations']])
        invalid = deepcopy(empty['certificate'])
        invalid['cancellations'] = [[0, loops[0]]]
        invalid['surviving_two_handles'] = [i for i in range(len(zero['core']['handles2']))
                                           if i != loops[0]]
        self.assertIsNone(replay_core_dual_forest(zero, invalid))
        positive = source(raw, vertex_link_coordinates(raw, interior=1))['geometry']
        proof = core_dual_forest(positive)['certificate']
        loop_roots = {zero['core']['handles2'][i]['edge'] for i in loops}
        pairs = [proof['source_sides'][h['id']] for h in positive['core']['handles2']
                 if h['edge'] in loop_roots]
        self.assertEqual(sorted(pairs), [[-1, 0], [0, -1]])
        self.assertIsNotNone(replay_core_dual_forest(positive, proof))

    def test_weighted_forest_enables_later_source_handlebody_cancellation(self):
        raw = interior_loop_torus()
        for boundary in (0, 1):
            rows = vertex_link_coordinates(raw, boundary=boundary)
            bfs = normal_cut_handlebodies(raw, rows, dual_strategy='bfs')
            weighted = normal_cut_handlebodies(raw, rows, dual_strategy='max_weight',
                                              record_certificate=True)
            self.assertEqual(bfs['status'], 'INCONCLUSIVE')
            self.assertEqual(bfs['reason'], 'raw_cancellation_stalled')
            self.assertEqual(weighted['status'], 'COMPLETE')
            expected = ([dict(genus=0, multiplicity=1)] if boundary else [])
            expected.append(dict(genus=1, multiplicity=1))
            self.assertEqual(weighted['census']['histogram'], expected)
            self.assertTrue(verify_normal_cut_handlebodies(raw, rows,
                                                          weighted['certificate']))

    def test_positive_binary_scale_reuses_both_forest_certificates(self):
        raw = interior_loop_torus()
        rows = vertex_link_coordinates(raw, interior=1, boundary=1)
        small = source(raw, rows)
        huge_rows = [[(1 << 16384) * x for x in row] for row in rows]
        huge = source(raw, json_safe(huge_rows))
        for strategy in ('bfs', 'max_weight'):
            proof = core_dual_forest(small['geometry'], strategy=strategy)['certificate']
            self.assertEqual(core_dual_forest(huge['geometry'], strategy=strategy)['certificate'],
                             proof)
            self.assertIsNotNone(replay_core_dual_forest(huge['geometry'], proof))

    def test_bfs_reuse_for_distinct_surfaces_with_equal_edge_support(self):
        raw, basis = interior_vertex_torus()
        sphere = source(raw, basis['sphere'])['geometry']
        disk = source(raw, basis['boundary_disk'])['geometry']
        self.assertNotEqual(sphere['core']['handles0'], disk['core']['handles0'])
        proof = core_dual_forest(sphere)['certificate']
        self.assertEqual(core_dual_forest(disk)['certificate'], proof)
        self.assertIsNotNone(replay_core_dual_forest(disk, proof))

    def test_relabelled_source_edges_and_quad_types(self):
        raw, basis = interior_vertex_torus()
        rows = basis['mobius']
        rng = random.Random(20261012)
        for _ in range(8):
            permutation = list(range(len(rows)))
            rng.shuffle(permutation)
            vertices = [rng.sample(range(4), 4) for _ in rows]
            changed, coords = relabel(raw, rows, permutation, vertices)
            geometry = source(changed, coords)['geometry']
            for strategy in ('bfs', 'max_weight'):
                result = core_dual_forest(geometry, strategy=strategy)
                self.assertEqual(result['status'], 'COMPLETE')
                self.assertIsNotNone(replay_core_dual_forest(geometry, result['certificate']))

    def test_independent_source_replay_with_producers_disabled(self):
        raw, basis = interior_vertex_torus()
        rows = [[3 * x for x in row] for row in basis['mobius']]
        parallelity = source(raw, rows)
        dual = core_dual_forest(parallelity['geometry'])
        proof = json.loads(json.dumps(json_safe(dual['certificate'])))
        names = (
            'fastunknot.core_dual_forest.core_dual_forest',
            'fastunknot.core_dual_forest.dual_forest_plan',
            'fastunknot.core_dual_forest._source_sides',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'fastunknot.normal_parallelity_geometry._parallelity_geometry',
        )
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_parallelity(raw, rows,
                                                         parallelity['certificate']))
            self.assertEqual(replay_core_dual_forest(parallelity['geometry'], proof),
                             dual['core'])

    def test_mutated_certificates_and_source_cannot_bypass_replay(self):
        raw, basis = interior_vertex_torus()
        rows = basis['sphere']
        parallelity = source(raw, rows)
        geometry = parallelity['geometry']
        good = core_dual_forest(geometry)['certificate']
        mutants = []
        for key, value in [('schema', 'bad'), ('source_sides', []),
                           ('cancellations', []), ('surviving_two_handles', [])]:
            bad = deepcopy(good)
            bad[key] = value
            mutants.append(bad)
        bad = deepcopy(good)
        bad['cancellations'] *= 2
        mutants.append(bad)
        for value in (True, -2, 100000, '0xnope'):
            bad = deepcopy(good)
            bad['cancellations'][0][0] = value
            mutants.append(bad)
        bad = deepcopy(good)
        bad['source_sides'][good['cancellations'][0][1]] = [-1, -1]
        mutants.append(bad)
        for bad in mutants:
            self.assertIsNone(replay_core_dual_forest(geometry, bad))
        forged = deepcopy(parallelity['certificate'])
        forged['geometry']['core']['handles3'][0]['link_triangles'][0][1] ^= 1
        self.assertFalse(verify_normal_cut_parallelity(raw, rows, forged))
        forged = deepcopy(parallelity['certificate'])
        forged['geometry']['core']['handles2'][0]['rank'] += 1
        self.assertFalse(verify_normal_cut_parallelity(raw, rows, forged))

    def test_alternative_valid_source_forest_and_hex_integer_codec(self):
        raw, _ = interior_vertex_torus()
        geometry = source(raw, vertex_link_coordinates(raw))['geometry']
        good = core_dual_forest(geometry)['certificate']
        candidates = [i for i, side in enumerate(good['source_sides'])
                      if side in ([0, -1], [-1, 0])]
        self.assertGreater(len(candidates), 1)
        other = deepcopy(good)
        edge = candidates[-1]
        other['cancellations'] = [['+0X0', hex(edge)]]
        other['surviving_two_handles'] = [hex(i) for i in range(len(good['source_sides']))
                                         if i != edge]
        self.assertIsNotNone(replay_core_dual_forest(geometry, other))

    def test_no_three_handles_is_identity_and_callback_is_propagated(self):
        raw, rows = layered_torus(1)
        geometry = source(raw, rows)['geometry']
        result = core_dual_forest(geometry)
        self.assertEqual(result['core'], geometry['core'])
        self.assertEqual(result['certificate']['cancellations'], [])
        self.assertIsNotNone(replay_core_dual_forest(geometry, result['certificate']))

        class Cancel:
            def __bool__(self):
                return False

            def __call__(self):
                raise ValueError('cancelled')

        with self.assertRaisesRegex(ValueError, 'cancelled'):
            core_dual_forest(geometry, check=Cancel())
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            replay_core_dual_forest(geometry, result['certificate'], check=Cancel())

    def test_maximum_weight_against_exhaustive_small_multigraph_trees(self):
        points = [-1, 0, 1, 2]
        simple = list(combinations(points, 2))
        for mask in range(1 << len(simple)):
            sides = [list(edge) for i, edge in enumerate(simple) if mask >> i & 1]
            sides += [[v, v] for v in points]
            if sides:
                sides += [list(sides[0])]
            for seed in (0, 7):
                costs = [(i * 3 + seed) % 11 for i in range(len(sides))]
                best = None
                for selected in combinations(range(len(sides)), 3):
                    reached = {-1}
                    while True:
                        enlarged = reached | {v for i in selected for v in sides[i]
                                              if any(w in reached for w in sides[i])}
                        if enlarged == reached:
                            break
                        reached = enlarged
                    if reached == set(points):
                        value = sum(costs[i] for i in selected)
                        best = value if best is None else max(best, value)
                plan = dual_forest_plan(sides, 3, strategy='max_weight', weights=costs)
                if best is None:
                    self.assertTrue(plan['unreachable_three_handles'])
                else:
                    self.assertFalse(plan['unreachable_three_handles'])
                    self.assertEqual(plan['removed_weight'], best)
                    self.assertEqual(len(plan['cancellations']), 3)


if __name__ == '__main__':
    unittest.main()
