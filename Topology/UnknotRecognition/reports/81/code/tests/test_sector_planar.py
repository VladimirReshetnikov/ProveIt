"""Exact planar fan coverage, degeneracies, limits, and native ray checks."""

from copy import deepcopy
from fractions import Fraction
from itertools import combinations, product
import random
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import (
    SearchLimit, _primitive, build_sector_kernel, sector_rays,
)
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.sector_planar import (
    _Work, _clip_polygon, enumerate_planar_sector,
    sector_planar_plan, sector_planar_rays,
)


def solid_torus():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]},
        None, None,
    ]]}


def attach_ball(raw):
    result = deepcopy(raw)
    faces = result['tetrahedra']
    source, face = next((i, f) for i, rows in enumerate(faces)
                        for f, target in enumerate(rows) if target is None)
    target = len(faces)
    faces.append([None]*4)
    faces[source][face] = dict(tetrahedron=target, permutation=[0, 1, 2, 3])
    faces[target][face] = dict(tetrahedron=source, permutation=[0, 1, 2, 3])
    return result


def vector_set(rays):
    return {tuple(x for row in ray for x in row) for ray in rays}


def fake_kernel(basis, group_vectors):
    potentials = {}
    groups = []
    for vectors in group_vectors:
        group = []
        for vector in vectors:
            corner = len(potentials)
            group.append(corner)
            potentials[corner] = tuple(map(Fraction, vector))
        groups.append(tuple(group))
    return SimpleNamespace(basis=tuple(tuple(map(Fraction, row)) for row in basis),
        classes=tuple(potentials), groups=tuple(groups), potentials=potentials)


def plan_directions(plan):
    output = set()
    for point in plan['points']:
        q = list(plan['q_origin'])
        for value, direction in zip(point, plan['q_directions']):
            q = [a+value*b for a, b in zip(q, direction)]
        output.add(_primitive(q))
    return output


def literal_three_dimensional_rays(kernel):
    """Small independent arrangement oracle with exact active-normal rank.

    It intentionally forms every pairwise equality, then filters by the
    rank of inequalities active at the true minima.  This is a slow oracle,
    not the clipping or overlay algorithm being tested.
    """
    basis = kernel.basis
    width = len(basis[0])

    def project(row):
        return tuple(sum(x*y for x, y in zip(row, column)) for column in basis)

    normals = [project(tuple(int(i == j) for i in range(width)))
               for j in range(width)]
    for group in kernel.groups:
        for a, b in combinations(group, 2):
            normals.append(project(tuple(x-y for x, y in
                zip(kernel.potentials[a], kernel.potentials[b]))))
    normals = tuple(set(_primitive(row) for row in normals if any(row)))
    output = set()
    for a, b in combinations(normals, 2):
        z = (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2],
             a[0]*b[1]-a[1]*b[0])
        if not any(z):
            continue
        q = _primitive(sum(z[j]*basis[j][i] for j in range(3))
                       for i in range(width))
        if any(x < 0 for x in q):
            continue
        active = [project(tuple(int(i == j) for i in range(width)))
                  for j, value in enumerate(q) if not value]
        for group in kernel.groups:
            values = {c: sum(x*y for x, y in zip(kernel.potentials[c], q))
                      for c in group}
            minimum = min(values.values())
            corners = [c for c in group if values[c] == minimum]
            for corner in corners[1:]:
                active.append(project(tuple(x-y for x, y in
                    zip(kernel.potentials[corner], kernel.potentials[corners[0]]))))
        if any((u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2],
                u[0]*v[1]-u[1]*v[0]) != (0, 0, 0)
               for u, v in combinations(active, 2)):
            output.add(q)
    return output


class PlanarGeometryTests(unittest.TestCase):
    def test_closed_clipping_preserves_polygon_segment_point_and_empty(self):
        work = _Work(lambda: None, None, {})
        square = tuple(tuple(map(Fraction, point))
                       for point in [(0, 0), (1, 0), (1, 1), (0, 1)])
        triangle = _clip_polygon(square, (Fraction(1), -1, -1), work)
        self.assertEqual(triangle, ((0, 0), (1, 0), (0, 1)))
        segment = _clip_polygon(triangle, (Fraction(0), -1, 0), work)
        self.assertEqual(segment, ((0, 0), (0, 1)))
        point = _clip_polygon(segment, (Fraction(0), 0, -1), work)
        self.assertEqual(point, ((0, 0),))
        self.assertEqual(_clip_polygon(point, (Fraction(-1), 0, 0), work), ())
        self.assertEqual(_clip_polygon(square, (Fraction(0), 0, 0), work), square)

    def test_raw_nullity_three_all_feasible_dimensions(self):
        cases = [
            ([(1, -1, 0, 0), (0, 1, -1, 0), (0, 0, 1, -1)], -1),
            ([(1, -1, 0, 0), (0, 1, -1, 0), (0, 0, -2, 1)], -1),
            ([(1, -1, 0, 0, 0), (0, 0, 1, -1, 0), (0, 0, 0, 0, 1)], 0),
            ([(1, -1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)], 1),
            ([(1, 0, 0), (0, 1, 0), (0, 0, 1)], 2),
        ]
        for basis, expected in cases:
            kernel = fake_kernel(basis, [])
            plan = sector_planar_plan(kernel)
            with self.subTest(basis=basis):
                self.assertEqual(plan['matching_dimension'], 3)
                self.assertEqual(plan['section_dimension'], expected)
                self.assertEqual(len(plan['points']), max(0, expected+1))

    def test_lower_dimensional_minimizers_and_boundary_ties_add_no_spurious_rays(self):
        identity = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        kernel = fake_kernel(identity, [[(0, 0, 0), (1, 0, 0), (0, 1, 0),
                                          (0, 0, 1), (1, 1, 1), (0, 0, 0)]])
        stats = {}
        plan = sector_planar_plan(kernel, stats=stats)
        self.assertEqual(plan_directions(plan), {(1, 0, 0), (0, 1, 0), (0, 0, 1)})
        self.assertEqual(stats['minimum_cells'], 1)
        self.assertEqual(stats['skeleton_segments'], 0)
        self.assertGreater(stats['discarded_lower_dimensional_cells'], 0)

    def test_raw_three_dimensional_segment_has_exact_minimum_switch(self):
        basis = [(1, -1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
        kernel = fake_kernel(basis, [[(0, 0, 1, 0), (0, 0, 0, 1),
                                      (0, 0, 1, 1), (0, 0, 1, 0)]])
        plan = sector_planar_plan(kernel)
        self.assertEqual(plan['section_dimension'], 1)
        self.assertEqual(plan_directions(plan),
                         {(0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 1, 1)})

    def test_orthogonal_strip_family_is_quadratic_and_bound_is_exact(self):
        # q0+q1=q2+q3=1/2 is a projective square.  Two independent
        # affine lower envelopes draw a rectangular grid on that square.
        basis = [(1, -1, 0, 0), (1, 0, 1, 0), (1, 0, 0, 1)]
        for count in range(2, 8):
            groups = []
            for coordinate in (0, 2):
                forms = []
                for index in range(count):
                    form = [Fraction(index*index, 2*count)]*4
                    form[coordinate] -= 2*index
                    forms.append(form)
                groups.append(forms)
            kernel = fake_kernel(basis, groups)
            stats = {}
            plan = sector_planar_plan(kernel, stats=stats)
            with self.subTest(count=count):
                self.assertEqual(len(plan['domain']), 4)
                self.assertEqual(len(plan['points']), (count+1)**2)
                self.assertEqual(stats['output_bound'], (count+1)**2)
                self.assertEqual(stats['skeleton_segments'], 2*(count-1))
                self.assertEqual(stats['segment_intersection_tests'], (count-1)**2)

    def test_coincident_and_collinear_overlay_segments(self):
        basis = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        kernel = fake_kernel(basis, [[(1, 0, 0), (0, 1, 0)],
                                      [(2, 0, 0), (0, 2, 0)],
                                      [(1, 1, 0), (0, 0, 1)]])
        plan = sector_planar_plan(kernel)
        self.assertEqual(plan_directions(plan), literal_three_dimensional_rays(kernel))
        self.assertEqual(len(plan['skeleton']), 2)

    def test_random_minimum_subdivisions_against_inactive_arrangement_oracle(self):
        rng = random.Random(610093)
        basis = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        for number in range(100):
            vectors = [[tuple(rng.randrange(-3, 5) for _ in range(3))
                        for _ in range(rng.randrange(2, 6))]
                       for _ in range(rng.randrange(1, 4))]
            kernel = fake_kernel(basis, vectors)
            with self.subTest(number=number):
                self.assertEqual(plan_directions(sector_planar_plan(kernel)),
                                 literal_three_dimensional_rays(kernel))


class PlanarNativeTests(unittest.TestCase):
    def test_all_small_capped_sectors_against_current_arrangement(self):
        raw = solid_torus()
        checked = 0
        for count in range(1, 5):
            for choices in product((-1, 0, 1, 2), repeat=count):
                allowed = [(i, typ) for i, typ in enumerate(choices) if typ >= 0]
                kernel = build_sector_kernel(raw, allowed)
                if len(kernel.basis) > 3:
                    continue
                expected = vector_set(sector_rays(kernel, phase='standard',
                                                  method='arrangement'))
                stats = {}
                actual = vector_set(sector_planar_rays(kernel, stats=stats))
                with self.subTest(count=count, choices=choices):
                    self.assertEqual(actual, expected)
                    self.assertEqual(stats['candidate_lifts'], len(actual))
                    self.assertEqual(stats['projected_lifts'], len(actual))
                    self.assertLessEqual(len(actual), stats['output_bound'])
                checked += 1
            raw = attach_ball(raw)
        self.assertEqual(checked, 259)

    def test_small_native_sectors_against_independent_dense_model(self):
        raw = solid_torus()
        for count in (1, 2):
            for choices in product((-1, 0, 1, 2), repeat=count):
                allowed = [(i, typ) for i, typ in enumerate(choices) if typ >= 0]
                expected = dense_reference_rays(dense_sector_model(raw, allowed),
                                                'standard')
                rays, stats = enumerate_planar_sector(raw, allowed)
                self.assertEqual(vector_set(rays),
                                 vector_set(value[0] for value in expected.values()))
                self.assertGreater(stats['kernel_checkpoints'], 0)
            raw = attach_ball(raw)

    def test_single_group_needs_no_pair_overlay_and_no_rank_or_old_lift(self):
        raw = attach_ball(attach_ball(solid_torus()))
        kernel = build_sector_kernel(raw, [(0, 2), (1, 1), (2, 1)])
        expected = vector_set(sector_rays(kernel, phase='standard', method='arrangement'))
        self.assertEqual(len(kernel.basis), 3)
        self.assertEqual(len(kernel.groups), 1)
        with patch('fastunknot.normal_sector._hyperplanes',
                   side_effect=AssertionError('inactive hyperplanes')):
            with patch.object(kernel, 'is_standard_ray',
                              side_effect=AssertionError('rank filter')):
                with patch.object(kernel, 'lift',
                                  side_effect=AssertionError('uncached lift')):
                    stats = {}
                    rays = list(sector_planar_rays(kernel, stats=stats))
        self.assertEqual(vector_set(rays), expected)
        self.assertEqual(stats.get('segment_intersection_tests', 0), 0)
        self.assertEqual(stats['potential_projections'], 3*len(kernel.classes))
        self.assertLessEqual(len(rays),
                            len(sector_planar_plan(kernel)['domain'])
                            + 2*stats['skeleton_segments'])

    def test_large_rational_basis_change_preserves_complete_rays(self):
        raw = attach_ball(attach_ball(solid_torus()))
        kernel = build_sector_kernel(raw, [(0, 2), (1, 1), (2, 0)])
        expected = vector_set(sector_planar_rays(kernel))
        a, b, c = kernel.basis
        denominator = 2**521 + 7
        kernel.basis = (
            tuple(x+Fraction(y, denominator) for x, y in zip(a, b)),
            tuple(y+Fraction(z, denominator) for y, z in zip(b, c)),
            tuple(z+Fraction(x, denominator) for z, x in zip(c, a)))
        self.assertEqual(vector_set(sector_planar_rays(kernel)), expected)

    def test_exact_work_allowance_and_resource_exhaustion(self):
        raw = attach_ball(attach_ball(solid_torus()))
        allowed = [(0, 2), (1, 1), (2, 0)]
        expected, stats = enumerate_planar_sector(raw, allowed)
        allowance = stats['work_units']
        actual, repeated = enumerate_planar_sector(raw, allowed, max_work=allowance)
        self.assertEqual(actual, expected)
        self.assertEqual(repeated, stats)
        with self.assertRaises(SearchLimit):
            enumerate_planar_sector(raw, allowed, max_work=allowance-1)
        with self.assertRaises(SearchLimit):
            enumerate_planar_sector(raw, allowed, max_work=0)
        for invalid in (-1, True, 2.5):
            with self.assertRaises(ValueError):
                enumerate_planar_sector(raw, allowed, max_work=invalid)

    def test_false_valued_callback_cancellation_propagates(self):
        class Cancel:
            def __init__(self):
                self.calls = 0

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == 17:
                    raise RuntimeError('cancel planar query')

        with self.assertRaisesRegex(RuntimeError, 'cancel planar query'):
            enumerate_planar_sector(solid_torus(), [(0, 2)], check=Cancel())

    def test_matching_nullity_above_three_is_rejected(self):
        kernel = fake_kernel([(1, 0, 0, 0), (0, 1, 0, 0),
                              (0, 0, 1, 0), (0, 0, 0, 1)], [])
        with self.assertRaises(ValueError):
            sector_planar_plan(kernel)


if __name__ == '__main__':
    unittest.main()
