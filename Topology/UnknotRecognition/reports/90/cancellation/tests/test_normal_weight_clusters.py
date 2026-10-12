"""Independent coverage, disconnected products, exact limits and certificate replay."""
from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import json
import random
import unittest
from unittest.mock import patch

import bootstrap
from fastunknot.normal_weight_clusters import (
    cluster_defect_search, enumerate_cluster_candidates, prepare_clusters,
    support_components, _connected_levels, _square_solve,
    _Budget, _support_rows, _exceptional,
)
from fastunknot.normal_weight_defect import enumerate_weight_subspace
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.normal_sector import build_sector_kernel, SearchLimit
from fastunknot.normal_vertex_gate import verify_vertex_disc_certificate
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.fixtures import layered_torus, boundary_cap


def flat(rows):
    return tuple(x for row in rows for x in row)


def standard_vertex(raw, rows):
    support = [(t, q) for t, row in enumerate(rows)
               for q in range(3) if row[4+q]]
    return build_sector_kernel(raw, support).is_standard_ray(rows)


def admissible_class(context, rows, maximum, components):
    data = _coordinates(context.prepared, rows, lambda: None)
    delta = {e: data['weights'][e]-context.baseline[e] for e in context.edges}
    if any(value < 0 or value % 2 for value in delta.values()):
        return False
    support = tuple(e for e in context.edges if delta[e])
    return (len(support) <= maximum
            and len(support_components(context, support)) <= components)


class NormalWeightClusterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = json.loads((bootstrap.REPO/
            'synthesis/data/coherent-obstruction-certificate.json').read_text())
        cls.obstruction = cls.record['moves'][-1]['triangulation']
        cls.disconnected = json.loads((bootstrap.HERE/
            'artifacts/disconnected_disc.json').read_text())

    def test_small_sources_match_independent_subspace_enumeration(self):
        rng = random.Random(261012229)
        raw, _ = layered_torus(2)
        fixtures = [layered_torus(1)[0], raw]
        for _ in range(3):
            sites = [(t, f) for t, row in enumerate(raw['tetrahedra'])
                     for f, gluing in enumerate(row)
                     if gluing is not None and gluing['tetrahedron'] != t]
            raw = pachner_23(raw, *rng.choice(sites))['triangulation']
            fixtures.append(raw)
        fixtures.append(self.obstruction)
        for raw in fixtures:
            with self.subTest(tetrahedra=len(raw['tetrahedra'])):
                context = prepare_clusters(raw)
                brute = {}
                for size in range(3):
                    for support in combinations(context.edges, size):
                        rows, _ = enumerate_weight_subspace(raw, list(support))
                        for candidate in rows:
                            if admissible_class(context, candidate, 2, 2):
                                brute[flat(candidate)] = candidate
                expected = {key for key, rows in brute.items() if standard_vertex(raw, rows)}
                result = enumerate_cluster_candidates(raw, max_defect=2, max_components=2)
                self.assertEqual(result['status'], 'COMPLETE')
                actual = {flat(rows) for rows in result['coordinates']
                          if standard_vertex(raw, rows)}
                self.assertEqual(actual, expected)

    def test_disconnected_vertex_disc_needs_two_profile_components(self):
        raw = self.disconnected['triangulation']
        expected = self.disconnected['coordinates']
        context = prepare_clusters(raw)
        self.assertEqual(support_components(context, [47, 53]), ((47,), (53,)))
        one = enumerate_cluster_candidates(raw, max_defect=2, max_components=1)
        two = enumerate_cluster_candidates(raw, max_defect=2, max_components=2)
        self.assertEqual(one['status'], 'COMPLETE')
        self.assertEqual(two['status'], 'COMPLETE')
        self.assertNotIn(expected, one['coordinates'])
        self.assertIn(expected, two['coordinates'])
        found = cluster_defect_search(raw, max_defect=2, max_components=2)
        self.assertEqual(found['status'], 'DISC_FOUND')
        self.assertEqual(found['coordinates'], expected)
        self.assertEqual(found['cancellation_components'], [[47], [53]])
        missed = cluster_defect_search(raw, max_defect=2, max_components=1)
        self.assertEqual(missed['status'], 'NO_VERTEX_DISC_IN_CANCELLATION_CLASS')

    def test_disconnected_counterexample_matches_brute_support_search(self):
        raw = self.disconnected['triangulation']
        rows, _ = enumerate_weight_subspace(raw, [47, 53])
        self.assertIn(self.disconnected['coordinates'], rows)
        context = prepare_clusters(raw)
        delta = self.disconnected['increments']
        self.assertTrue(all(int(value) > 0 and int(value) % 2 == 0 for value in delta.values()))
        self.assertEqual(len(support_components(context, map(int, delta))), 2)
        self.assertTrue(standard_vertex(raw, self.disconnected['coordinates']))

    def test_exceptional_homogeneous_branch_matches_full_coordinate_space(self):
        raw, _ = layered_torus(1)
        context = prepare_clusters(raw)
        support = context.edges
        stats = dict(work=0, systems=0, homogeneous_systems=0,
                     duplicate_solutions=0, local_reconstructions=0)
        budget = _Budget(lambda: None, {}, stats)
        candidates = list(_exceptional(context, support,
            _support_rows(context, support, budget), budget, stats))
        rays, _ = enumerate_weight_subspace(raw, list(support))
        expected = {flat(rows) for rows in rays
                    if all(_coordinates(context.prepared, rows, lambda: None)['weights'].values())}
        actual = {flat(rows) for rows in candidates}
        self.assertEqual(actual, expected)
        self.assertGreater(stats['homogeneous_systems'], 0)

    def test_coherent_case_and_zero_component_budget(self):
        for count in (1, 2, 16, 64):
            raw, expected = layered_torus(count)
            result = cluster_defect_search(raw, max_defect=0, max_components=0)
            self.assertEqual(result['status'], 'DISC_FOUND')
            self.assertEqual(result['coordinates'], expected)
            self.assertEqual(result['stats']['systems'], 0)
        result = cluster_defect_search(self.obstruction, max_defect=2, max_components=0)
        self.assertEqual(result['status'], 'NO_VERTEX_DISC_IN_CANCELLATION_CLASS')
        oversized = cluster_defect_search(self.obstruction, max_defect=1,
                                         max_components=2**8192)
        self.assertEqual(oversized['status'], 'DISC_FOUND')
        self.assertEqual(oversized['stats']['max_components'], 1)

    def test_exact_global_limits_include_positive_replay(self):
        reference = cluster_defect_search(self.obstruction, max_defect=1)
        self.assertEqual(reference['status'], 'DISC_FOUND')
        for name in ('work', 'systems', 'supports', 'combinations'):
            used = reference['stats'][name]
            with self.subTest(limit=name, used=used):
                self.assertGreater(used, 0)
                lower = cluster_defect_search(self.obstruction, max_defect=1,
                    **{'max_'+name: used-1})
                exact = cluster_defect_search(self.obstruction, max_defect=1,
                    **{'max_'+name: used})
                self.assertEqual(lower['status'], 'INCONCLUSIVE')
                self.assertNotIn('certificate', lower)
                self.assertEqual(exact['status'], 'DISC_FOUND')
                self.assertEqual(lower['stats'][name], used-1)
        raw, _ = layered_torus(1)
        self.assertEqual(cluster_defect_search(raw, max_defect=0,
            max_combinations=0)['status'], 'INCONCLUSIVE')
        partial = enumerate_cluster_candidates(self.obstruction, max_defect=2,
                                               max_systems=0)
        self.assertEqual(partial['status'], 'INCONCLUSIVE')

    def test_external_cancellation_and_immutability(self):
        original = deepcopy(self.obstruction)
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('external cancellation')
        with self.assertRaisesRegex(ValueError, 'external cancellation'):
            cluster_defect_search(self.obstruction, max_defect=1, check=Cancel())
        def cancel_limit():
            raise SearchLimit('external SearchLimit')
        with self.assertRaisesRegex(SearchLimit, 'external SearchLimit'):
            cluster_defect_search(self.obstruction, max_defect=1, check=cancel_limit)
        result = cluster_defect_search(self.obstruction, max_defect=1)
        self.assertEqual(result['status'], 'DISC_FOUND')
        self.assertEqual(self.obstruction, original)

    def test_strict_option_validation_and_multiple_vertices(self):
        for kwargs in ({'max_defect': True}, {'max_defect': -1},
                       {'max_defect': 1, 'max_components': False},
                       {'max_defect': 1, 'max_work': 1.5},
                       {'max_defect': 1, 'max_systems': -1},
                       {'max_defect': 1000}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                cluster_defect_search(self.obstruction, **kwargs)
        raw, coordinates = layered_torus(2)
        capped, _ = boundary_cap(raw, coordinates)
        with self.assertRaisesRegex(Exception, 'one global vertex'):
            cluster_defect_search(capped, max_defect=1)

    def test_independent_replay_disables_all_producers(self):
        found = cluster_defect_search(self.obstruction, max_defect=1)
        with patch('fastunknot.normal_weight_clusters.cluster_defect_search',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_vertex_gate.produce_vertex_disc_certificate',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_vertex_gate._find_rank_minor',
                   side_effect=AssertionError):
            self.assertTrue(verify_vertex_disc_certificate(
                self.obstruction, found['coordinates'], found['certificate']))
        forged = deepcopy(found['certificate'])
        forged['minor_determinant'] = '0x0'
        self.assertFalse(verify_vertex_disc_certificate(
            self.obstruction, found['coordinates'], forged))
        wrong = deepcopy(found['coordinates'])
        wrong[0][0] += 1
        self.assertFalse(verify_vertex_disc_certificate(
            self.obstruction, wrong, found['certificate']))

    def test_connected_enumeration_matches_exhaustive_subset_test(self):
        context = prepare_clusters(self.obstruction)
        levels = dict(_connected_levels(context, 4, lambda: None))
        for size in range(1, 5):
            expected = {support for support in combinations(context.edges, size)
                        if len(support_components(context, support)) == 1}
            self.assertEqual(set(levels[size]), expected)
        self.assertLessEqual(max(map(len, context.graph.values())), 5*context.degree)

    def test_binary_arithmetic_does_not_expand_multiplicity(self):
        huge = 2**8192+3**4000
        matrix = [[2, -1, 0], [0, 2, -1], [-1, 0, 2]]
        rhs = [huge, -huge+7, 2*huge]
        answer = _square_solve(matrix, rhs, lambda: None)
        self.assertIsNotNone(answer)
        for row, value in zip(matrix, rhs):
            self.assertEqual(sum(x*y for x, y in zip(row, answer)), value)
        self.assertLessEqual(max(x.numerator.bit_length() for x in answer),
                             huge.bit_length()+5)
        self.assertIsNone(_square_solve([[1, 1], [2, 2]], [0, 0], lambda: None))


if __name__ == '__main__':
    unittest.main()
