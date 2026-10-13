"""Exact compatibility and resource tests for sparse sector preparation."""

from copy import deepcopy
from itertools import product
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector import _source_hash, build_sector_kernel, sector_rays
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.sector_sparse import PreparedSectorSource, build_sparse_sector_kernel
from normal_orbit_research.fixtures import (
    boundary_cap, interior_vertex_torus, layered_torus,
)


def all_sectors(tetrahedra):
    for choices in product(range(-1, 3), repeat=tetrahedra):
        yield [(i, q) for i, q in enumerate(choices) if q >= 0]


def ray_set(kernel, phase='standard'):
    return {tuple(x for row in surface for x in row)
            for surface in sector_rays(kernel, phase=phase, method='arrangement')}


class FalseCancellation:
    def __init__(self, calls=1):
        self.remaining = calls

    def __bool__(self):
        return False

    def __call__(self):
        self.remaining -= 1
        if self.remaining == 0:
            raise RuntimeError('sparse-sector cancellation')


class SparseSectorTests(unittest.TestCase):
    def assert_kernels_equal(self, left, right):
        for field in ('triangulation', 'prepared', 'support', 'corner_class',
                      'classes', 'groups', 'matrix', 'potentials', 'cycle_rows',
                      'basis'):
            self.assertEqual(getattr(left, field), getattr(right, field), field)
        for key, value in left.stats.items():
            self.assertEqual(value, right.stats[key], key)
        self.assertLessEqual(right.stats['dense_labels_materialized'], 4*len(right.support))
        self.assertLessEqual(right.stats['sparse_label_incidences'], 4*len(right.support))

    def test_all_small_sector_fields_and_rays(self):
        raw, vector = layered_torus(1)
        cap, _ = boundary_cap(raw, vector)
        for triangulation in (raw, cap, layered_torus(2)[0]):
            source = PreparedSectorSource(triangulation)
            for support in all_sectors(len(triangulation['tetrahedra'])):
                with self.subTest(t=len(triangulation['tetrahedra']), support=support):
                    old = build_sector_kernel(triangulation, support)
                    new = source.build(support)
                    self.assert_kernels_equal(old, new)
                    for phase in ('quadrilateral', 'standard'):
                        self.assertEqual(ray_set(old, phase), ray_set(new, phase))

    def test_interior_vertex_and_all_four_tetrahedron_sector_fields(self):
        raw, _ = interior_vertex_torus()
        source = PreparedSectorSource(raw)
        for support in all_sectors(4):
            with self.subTest(support=support):
                self.assert_kernels_equal(build_sector_kernel(raw, support),
                                          source.build(support))

    def test_independent_dense_reference_on_selected_sectors(self):
        raw, vector = layered_torus(1)
        cap, _ = boundary_cap(raw, vector)
        interior, _ = interior_vertex_torus()
        cases = [(raw, [(0, q)]) for q in range(3)]
        cases += [(cap, [(0, 2), (1, q)]) for q in range(3)]
        cases += [(interior, [(0, 1), (2, 1)]),
                  (layered_torus(4)[0], [(i, 2) for i in range(4)])]
        for triangulation, support in cases:
            with self.subTest(support=support):
                model = dense_sector_model(triangulation, support)
                new = build_sparse_sector_kernel(triangulation, support)
                for phase in ('quadrilateral', 'standard'):
                    expected = {tuple(x for row in rows for x in row)
                                for rows, _ in dense_reference_rays(model, phase).values()}
                    self.assertEqual(expected, ray_set(new, phase))

    def test_reusable_source_validates_once_and_preserves_input(self):
        raw, _ = layered_torus(3)
        saved = deepcopy(raw)
        with patch('fastunknot.sector_sparse._prepare', wraps=_prepare) as validate:
            source = PreparedSectorSource(raw)
            first = source.build([(0, 2), (1, 2), (2, 2)])
            second = source.build([(2, 2), (0, 2), (1, 2)])
            source.build([])
            self.assertEqual(validate.call_count, 1)
        self.assert_kernels_equal(first, second)
        self.assertEqual(raw, saved)
        self.assertIs(first.prepared, second.prepared)
        self.assertEqual(source.source_sha256, _source_hash(raw))
        with self.assertRaises(AttributeError):
            source.source_sha256 = '0'*64

    def test_sparse_support_on_a_larger_genuine_triangulation(self):
        raw, vector = layered_torus(1)
        for _ in range(39):
            raw, vector = boundary_cap(raw, vector)
        source = PreparedSectorSource(raw)
        for support in ([], [(0, 2)], [(39, 1)], [(0, 2), (39, 1)]):
            old = build_sector_kernel(raw, support)
            new = source.build(support)
            self.assert_kernels_equal(old, new)
            self.assertEqual(ray_set(old), ray_set(new))
            self.assertLessEqual(new.stats['dense_label_entries'], 4*len(support)**2)
        self.assertGreater(source.build([(0, 2)]).stats['precompiled_equations'], 100)

    def test_empty_sector_keeps_shared_immutable_zero_potentials(self):
        raw, _ = interior_vertex_torus()
        kernel = build_sparse_sector_kernel(raw, [])
        self.assertEqual(kernel.groups, ())
        self.assertEqual(kernel.basis, ())
        self.assertEqual(kernel.stats['removed_link_factors'], 2)
        zeros = list(kernel.potentials.values())
        self.assertTrue(zeros)
        self.assertTrue(all(value is zeros[0] for value in zeros))

    def test_false_valued_callback_and_reuse_after_interruption(self):
        raw, _ = layered_torus(3)
        with self.assertRaisesRegex(RuntimeError, 'sparse-sector cancellation'):
            PreparedSectorSource(raw, check=FalseCancellation())
        source = PreparedSectorSource(raw)
        for calls in (1, 3, 12):
            with self.subTest(calls=calls):
                with self.assertRaisesRegex(RuntimeError, 'sparse-sector cancellation'):
                    source.build([(0, 2), (1, 2), (2, 2)],
                                 check=FalseCancellation(calls))
        self.assert_kernels_equal(build_sector_kernel(raw, [(0, 2)]),
                                  source.build([(0, 2)]))
        with self.assertRaisesRegex(RuntimeError, 'sparse-sector cancellation'):
            build_sparse_sector_kernel(raw, [], check=FalseCancellation())

    def test_invalid_support_and_malformed_geometry(self):
        raw, _ = layered_torus(1)
        source = PreparedSectorSource(raw)
        bad = [None, '0', [(0, True)], [(0, 3)], [(1, 0)], [(0, 0), (0, 1)],
               [(0, 2), (0, 2)], [(0,)], [(0.0, 1)]]
        for support in bad:
            with self.subTest(support=support):
                with self.assertRaises(ValueError):
                    source.build(support)
        for malformed in ({}, {'tetrahedra': []}, {'tetrahedra': [[None]*4]}):
            with self.subTest(malformed=malformed):
                with self.assertRaises(ValueError):
                    PreparedSectorSource(malformed)


if __name__ == '__main__':
    unittest.main()
