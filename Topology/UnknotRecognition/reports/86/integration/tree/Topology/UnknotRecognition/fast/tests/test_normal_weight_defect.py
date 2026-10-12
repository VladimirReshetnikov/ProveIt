"""Exact edge-metric reconstruction, discovery, coverage and replay tests."""

from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from fastunknot.normal_sector import build_sector_kernel, enumerate_sector, SearchLimit
from fastunknot.normal_surface_geometry import _coordinates, _prepare, _quad, _EDGES
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.normal_weight_defect import (
    build_weight_subspace, discover_in_weight_subspace, enumerate_weight_subspace,
    local_coordinates_from_weights, one_edge_defect_search, weight_defect_search,
)
from normal_orbit_research.fixtures import layered_torus, boundary_cap

RECORD = Path(__file__).resolve().parents[2]/'synthesis/data/coherent-obstruction-certificate.json'


def flat(rows):
    return tuple(x for row in rows for x in row)


def weights_of_row(row):
    return [row[a]+row[b]+sum(row[4:])-row[4+_quad(a, b)] for a, b in _EDGES]


class NormalWeightDefectTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = json.loads(RECORD.read_text())
        cls.raw = cls.record['moves'][-1]['triangulation']

    def test_local_reconstruction_including_zero_faces_and_rational_rays(self):
        rng = random.Random(261012071)
        for _ in range(1000):
            row = [rng.randrange(9) for _ in range(4)]+[0, 0, 0]
            row[4+rng.randrange(3)] = rng.randrange(9)
            denominator = rng.randrange(1, 13)
            rational = [Fraction(x, denominator) for x in row]
            self.assertEqual(local_coordinates_from_weights(weights_of_row(rational)),
                             rational)
        self.assertEqual(local_coordinates_from_weights([1]*6),
                         [Fraction(1, 2)]*4+[0]*3)
        huge = [2**4096, 0, 3**2048, 0, 0, 5**1024, 0]
        self.assertEqual(local_coordinates_from_weights(weights_of_row(huge)), huge)

    def test_invalid_local_metrics_are_rejected(self):
        bad = [None, [], [1]*5, [True]*6, [1.0]*6, [-1]*6,
               [1, 0, 0, 0, 0, 1], [0, 1, 1, 3, 3, 2]]
        for value in bad:
            with self.subTest(value=value):
                with self.assertRaises(NormalOrbitError):
                    local_coordinates_from_weights(value)

    def test_dense_layered_meridians_need_no_exceptional_edge(self):
        for tetrahedra in (1, 2, 8, 32, 64):
            raw, expected = layered_torus(tetrahedra)
            result = weight_defect_search(raw, max_defect=0)
            self.assertEqual(result['status'], 'DISC_FOUND')
            self.assertEqual(result['coordinates'], expected)
            self.assertEqual(result['stats']['bases_attempted'], 1)
            self.assertEqual(result['stats']['peak_dimension'], 1)
            self.assertTrue(verify_normal_disk_count_certificate(
                raw, result['coordinates'], result['certificate']))

    def test_coherent_obstruction_is_escaped_by_one_exceptional_edge(self):
        zero = weight_defect_search(self.raw, max_defect=0)
        self.assertEqual(zero['status'], 'NO_VERTEX_DISC_UP_TO_EDGE_DEFECT')
        self.assertNotIn('certificate', zero)
        result = weight_defect_search(self.raw, max_defect=1)
        self.assertEqual(result['status'], 'DISC_FOUND')
        self.assertEqual(result['searched_edges'], [30])
        self.assertEqual(result['stats']['bases_attempted'], 71)
        self.assertEqual(result['stats']['subspaces_visited'], 11)
        prepared = _prepare(self.raw, lambda: None)
        baseline = _coordinates(prepared, self.record['family_certificate']['coordinates'],
                                lambda: None)['weights']
        weights = _coordinates(prepared, result['coordinates'], lambda: None)['weights']
        self.assertEqual({e: weights[e]-baseline[e] for e in weights if weights[e] != baseline[e]},
                         {30: 4})
        support = [(t, q) for t, row in enumerate(result['coordinates'])
                   for q in range(3) if row[4+q]]
        self.assertTrue(build_sector_kernel(self.raw, support).is_standard_ray(
            result['coordinates']))
        with patch('fastunknot.normal_weight_defect.weight_defect_search',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_weight_defect.normal_compressing_disk_count',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle._rank_one_cocycle_seed_details',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError):
            self.assertTrue(verify_normal_disk_count_certificate(
                self.raw, result['coordinates'], result['certificate']))

    def test_published_two_edge_disc_is_recovered(self):
        rows, stats = enumerate_weight_subspace(self.raw, [15, 18])
        self.assertIn(self.record['disc_coordinates'], rows)
        self.assertEqual(stats['peak_dimension'], 3)
        self.assertEqual(stats['peak_hyperplanes'], 15)
        self.assertEqual(stats['bases_attempted'], 105)
        self.assertEqual(stats['raw_hyperplanes'], 10+15*8)

    def test_global_one_edge_search_and_supplied_subspace_agree(self):
        optimized = one_edge_defect_search(self.raw)
        brute = weight_defect_search(self.raw, max_defect=1)
        supplied = discover_in_weight_subspace(self.raw, [30])
        self.assertEqual(optimized['status'], 'DISC_FOUND')
        self.assertEqual(optimized['coordinates'], brute['coordinates'])
        self.assertEqual(supplied['coordinates'], brute['coordinates'])
        self.assertEqual(optimized['edge_increment'], 4)
        self.assertEqual(optimized['stats']['bases_attempted'], 39)
        self.assertEqual(optimized['stats']['local_tetrahedron_queries'], 10)
        self.assertLess(optimized['stats']['bases_attempted'],
                        brute['stats']['bases_attempted'])
        for cap, expected in ((38, 'INCONCLUSIVE'), (39, 'DISC_FOUND')):
            self.assertEqual(one_edge_defect_search(self.raw, max_bases=cap)['status'],
                             expected)
        raw, disc = layered_torus(32)
        self.assertEqual(one_edge_defect_search(raw)['coordinates'], disc)

    def test_global_hyperplane_incidence_support_bound(self):
        from fastunknot.normal_weight_defect import _global_hyperplanes
        prepared = _prepare(self.raw, lambda: None)
        planes = _global_hyperplanes(prepared, lambda: None)
        self.assertTrue(all(0 < len(row) <= 4 for row in planes))
        self.assertLessEqual(len(planes), prepared['edges']+15*len(self.raw['tetrahedra']))

    def test_dependent_baseline_column_is_removed(self):
        raw, _ = layered_torus(1)
        prepared = _prepare(raw, lambda: None)
        edges = sorted(set(prepared['edge_roots']))
        subspace = build_weight_subspace(raw, edges)
        self.assertEqual(subspace.dimension, len(edges))
        rows, _ = enumerate_weight_subspace(raw, edges)
        expected = {flat([[1, 1, 1, 1, 0, 0, 0]])}
        for typ in range(3):
            rays, _ = enumerate_sector(raw, [(0, typ)])
            expected.update(flat(ray) for ray in rays)
        self.assertEqual({flat(row) for row in rows}, expected)

    def test_exact_size_padding_retains_smaller_defects(self):
        for size in (1, 2):
            result = weight_defect_search(self.raw, max_defect=size, exact_size=True)
            self.assertEqual(result['status'], 'DISC_FOUND')
            self.assertEqual(len(result['searched_edges']), size)
            self.assertTrue(verify_normal_disk_count_certificate(
                self.raw, result['coordinates'], result['certificate']))

    def test_global_limits_are_exact_and_never_prove_absence(self):
        for options in ({'max_bases': 70}, {'max_subspaces': 10},
                        {'max_bases': 0}, {'max_subspaces': 0}):
            result = weight_defect_search(self.raw, max_defect=1, **options)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        result = weight_defect_search(self.raw, max_defect=1, max_bases=71,
                                     max_subspaces=11, max_orbit_cycles=0)
        self.assertEqual(result['status'], 'DISC_FOUND')
        with self.assertRaises(SearchLimit):
            enumerate_weight_subspace(self.raw, [15, 18], max_bases=104)
        with patch('fastunknot.normal_weight_defect.normal_compressing_disk_count',
                   return_value={'status': 'INCONCLUSIVE'}):
            result = weight_defect_search(self.raw, max_defect=1)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)

    def test_bad_options_and_multi_vertex_sources_are_rejected(self):
        for options in ({'max_defect': True}, {'max_defect': -1}, {'max_defect': 11},
                        {'max_defect': 0, 'exact_size': 1},
                        {'max_defect': 0, 'max_bases': True},
                        {'max_defect': 0, 'max_subspaces': -1},
                        {'max_defect': 0, 'max_orbit_cycles': 1.5}):
            with self.subTest(options=options):
                with self.assertRaises(ValueError):
                    weight_defect_search(self.raw, **options)
        for edges in (None, [True], [30, 30], [-1], [1.5], [100]):
            with self.assertRaises(ValueError):
                build_weight_subspace(self.raw, edges)
        multi, _ = boundary_cap(*layered_torus(1))
        with self.assertRaisesRegex(NormalOrbitError, 'one global vertex'):
            weight_defect_search(multi, max_defect=0)

    def test_cancellation_propagates_and_input_is_not_mutated(self):
        original = deepcopy(self.raw)
        calls = [0]

        class Cancel:
            def __bool__(self):
                return False

            def __call__(self):
                calls[0] += 1
                if calls[0] == 100:
                    raise RuntimeError('test cancellation')

        with self.assertRaisesRegex(RuntimeError, 'test cancellation'):
            weight_defect_search(self.raw, max_defect=1, check=Cancel())
        weight_defect_search(self.raw, max_defect=1)
        self.assertEqual(self.raw, original)

    def test_wrong_coordinates_and_source_are_rejected_by_independent_replay(self):
        result = weight_defect_search(self.raw, max_defect=1)
        wrong = deepcopy(result['coordinates'])
        wrong[0][0] += 1
        self.assertFalse(verify_normal_disk_count_certificate(
            self.raw, wrong, result['certificate']))
        raw, _ = layered_torus(8)
        self.assertFalse(verify_normal_disk_count_certificate(
            raw, result['coordinates'], result['certificate']))


if __name__ == '__main__':
    unittest.main()
