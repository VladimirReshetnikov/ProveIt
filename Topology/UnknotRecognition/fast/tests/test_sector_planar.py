"""Exact planar geometry, genuine normal rays, and coverage regressions."""

from copy import deepcopy
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random
import sys
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector import SearchLimit, sector_rays
from fastunknot.sector_sparse import PreparedSectorSource
from fastunknot.sector_planar import (
    _clip_polygon, _encoded, certify_planar_sector, sector_planar_plan,
    sector_planar_rays,
)
from fastunknot.sector_planar_verify import (
    _feasible_vertices, verify_planar_sector_certificate,
)
from fastunknot.integer_codec import encoded_integer


def double_capped_torus():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]},
        {'tetrahedron': 1, 'permutation': [0, 1, 2, 3]},
        {'tetrahedron': 2, 'permutation': [0, 1, 2, 3]},
    ], [None, None, {'tetrahedron': 0, 'permutation': [0, 1, 2, 3]}, None],
       [None, None, None, {'tetrahedron': 0, 'permutation': [0, 1, 2, 3]}]]}


def ray_set(rays):
    return {tuple(x for row in ray for x in row) for ray in rays}


def abstract_kernel(groups, basis=None):
    if basis is None:
        basis = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    width = len(basis[0])
    potentials, classes, partition, roots = {}, [], [], []
    for vertex, forms in enumerate(groups):
        group = []
        for form in forms:
            corner = len(classes)
            classes.append(corner)
            group.append(corner)
            roots.append(vertex)
            potentials[corner] = form
        partition.append(tuple(group))
    return SimpleNamespace(basis=tuple(tuple(map(Fraction, b)) for b in basis),
        support=tuple((i, 0) for i in range(width)), classes=tuple(classes),
        groups=tuple(partition), potentials=potentials,
        prepared={'vertex_roots': roots})


class PlanarSectorTests(unittest.TestCase):
    def test_all_double_cap_sectors_match_complete_old_enumeration(self):
        tri = double_capped_torus()
        source = PreparedSectorSource(tri)
        found_three = False
        for kinds in product(range(4), repeat=3):
            support = [(i, kind) for i, kind in enumerate(kinds) if kind < 3]
            kernel = source.build(support)
            if len(kernel.basis) > 3:
                continue
            found_three |= len(kernel.basis) == 3
            with self.subTest(support=support):
                self.assertEqual(ray_set(sector_planar_rays(kernel)),
                                 ray_set(sector_rays(kernel, method='arrangement')))
                result = certify_planar_sector(tri, support, source=source)
                self.assertTrue(verify_planar_sector_certificate(tri, result['certificate']))
        self.assertTrue(found_three)

    def test_quadratic_grid_is_exact(self):
        for size in (1, 2, 3, 5, 10):
            first = [(j*j-8*size*j, j*j, j*j) for j in range(size)]
            second = [(j*j, j*j-8*size*j, j*j) for j in range(size)]
            plan = sector_planar_plan(abstract_kernel([first, second]))
            cuts = [Fraction(2*j+1, 8*size) for j in range(size-1)]
            expected = {(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)),
                        (Fraction(0), Fraction(1))}
            expected.update((x, y) for x in cuts for y in cuts)
            expected.update((x, 0) for x in cuts)
            expected.update((x, 1-x) for x in cuts)
            expected.update((0, y) for y in cuts)
            expected.update((1-y, y) for y in cuts)
            self.assertEqual(set(plan['points']), expected)
            self.assertEqual(len(plan['points']), size*size+2*size)

    def test_inactive_equalities_and_lower_dimensional_minima_are_ignored(self):
        for forms in [[(0, 0, 0), (2, 1, 1), (1, 2, 1)],
                      [(0, 0, 0), (0, 0, 0), (1, 0, 0), (0, 1, 0)]]:
            stats = {}
            plan = sector_planar_plan(abstract_kernel([forms]), stats=stats)
            self.assertEqual(len(plan['points']), 3)
            self.assertEqual(stats['internal_segments'], 0)

    def test_coincident_minimum_edges_do_not_make_false_vertices(self):
        forms = [(0, 0, 0), (-3, 1, 1), (-4, 4, 4)]
        single = sector_planar_plan(abstract_kernel([forms]))
        repeated = sector_planar_plan(abstract_kernel([forms, forms, forms]))
        self.assertEqual(single['points'], repeated['points'])

    def test_raw_three_dimensional_kernel_can_have_segment_point_or_empty_section(self):
        segment = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, -1))
        point = ((1, 0, 0, 0, 0), (0, 1, -1, 0, 0), (0, 0, 0, 1, -1))
        empty = ((1, -1, 0, 0, 0, 0), (0, 0, 1, -1, 0, 0),
                 (0, 0, 0, 0, 1, -1))
        for basis, dimension in ((segment, 1), (point, 0), (empty, -1)):
            width = len(basis[0])
            plan = sector_planar_plan(abstract_kernel([[(0,)*width]], basis))
            self.assertEqual(plan['section_dimension'], dimension)
            self.assertEqual(len(plan['points']), dimension+1 if dimension >= 0 else 0)

    def test_clipping_matches_independent_pair_intersection_oracle(self):
        rng = random.Random(873164)
        square = tuple(tuple(map(Fraction, p))
                       for p in ((0, 0), (1, 0), (1, 1), (0, 1)))
        for _ in range(180):
            constraints = [tuple(Fraction(rng.randrange(-4, 5)) for _ in range(3))
                           for _ in range(rng.randrange(1, 8))]
            polygon = square
            for form in constraints:
                polygon = _clip_polygon(polygon, form)
            self.assertEqual(polygon, _feasible_vertices(constraints, lambda: None))

    def test_complete_certificate_survives_json_and_rejects_missing_geometry(self):
        tri = double_capped_torus()
        result = certify_planar_sector(tri, [(0, 2), (1, 1), (2, 1)])
        proof = json.loads(json.dumps(result['certificate']))
        self.assertEqual(proof['matching_dimension'], 3)
        self.assertEqual(proof['section_dimension'], 2)
        self.assertTrue(verify_planar_sector_certificate(tri, proof))
        mutations = []
        for field, value in [('source_sha256', '0'*64), ('matching_dimension', 2),
                             ('section_dimension', 1), ('groups', []), ('rays', [])]:
            changed = deepcopy(proof)
            changed[field] = value
            mutations.append(changed)
        changed = deepcopy(proof)
        changed['groups'][0]['cells'].pop()
        mutations.append(changed)
        changed = deepcopy(proof)
        changed['groups'][0]['cells'].append(deepcopy(changed['groups'][0]['cells'][0]))
        mutations.append(changed)
        changed = deepcopy(proof)
        changed['rays'][0][0][0] += 1
        mutations.append(changed)
        for changed in mutations:
            self.assertFalse(verify_planar_sector_certificate(tri, changed))

    def test_limits_and_cancellation_never_certify_partial_coverage(self):
        tri = double_capped_torus()
        support = [(0, 2), (1, 1), (2, 1)]
        result = certify_planar_sector(tri, support, max_rays=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        kernel = PreparedSectorSource(tri).build(support)
        with self.assertRaises(SearchLimit):
            list(sector_planar_rays(kernel, max_rays=0))
        for limit in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                certify_planar_sector(tri, support, max_rays=limit)
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise ValueError('cancelled deliberately')
        with self.assertRaisesRegex(ValueError, 'cancelled deliberately'):
            certify_planar_sector(tri, support, check=Cancel())
        proof = certify_planar_sector(tri, support)['certificate']
        with self.assertRaisesRegex(ValueError, 'cancelled deliberately'):
            verify_planar_sector_certificate(tri, proof, check=Cancel())

    def test_mismatched_reused_source_is_rejected(self):
        tri = double_capped_torus()
        source = PreparedSectorSource(tri)
        changed = deepcopy(tri)
        changed['comment'] = 'different source serialization'
        with self.assertRaisesRegex(ValueError, 'does not match'):
            certify_planar_sector(changed, [], source=source)

    def test_large_rational_encoding_has_no_decimal_conversion_limit(self):
        value = Fraction(1, 2**20000+1)
        encoded = json.loads(json.dumps(_encoded(value)))
        self.assertEqual(Fraction(*(encoded_integer(x) for x in encoded)), value)


if __name__ == '__main__':
    unittest.main()
