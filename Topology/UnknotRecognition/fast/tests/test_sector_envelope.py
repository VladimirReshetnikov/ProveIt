"""Exact lower-envelope checks and independent normal-sector comparisons."""

from copy import deepcopy
from fractions import Fraction
from itertools import product
from pathlib import Path
import random
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector import (
    SearchLimit, build_sector_kernel, sector_rays,
)
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.sector_envelope import (
    _lower_envelope, _unit_section, sector_envelope_plan, sector_envelope_rays,
)


def solid_torus():
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]},
        None, None,
    ]]}


def attach_ball(raw):
    """Glue one tetrahedral ball to a boundary triangle, preserving manifold."""
    result = deepcopy(raw)
    tetrahedra = result['tetrahedra']
    source, face = next((i, f) for i, faces in enumerate(tetrahedra)
                        for f, gluing in enumerate(faces) if gluing is None)
    target = len(tetrahedra)
    tetrahedra.append([None] * 4)
    tetrahedra[source][face] = dict(tetrahedron=target, permutation=[0, 1, 2, 3])
    tetrahedra[target][face] = dict(tetrahedron=source, permutation=[0, 1, 2, 3])
    return result


def vectors(rows):
    return {tuple(x for row in surface for x in row) for surface in rows}


def hull_value(hull, point):
    active = hull[0]
    for piece in hull[1:]:
        if piece[2] > point:
            break
        active = piece
    return active[0] * point + active[1]


class SectorEnvelopeAlgebraTests(unittest.TestCase):
    def test_parallel_coincident_and_triple_ties(self):
        lines = [(2, 0), (2, 1), (2, 0), (1, 1), (0, 2)]
        self.assertEqual(_lower_envelope(lines),
                         ((Fraction(2), Fraction(0), None),
                          (Fraction(0), Fraction(2), Fraction(1))))
        self.assertEqual(_lower_envelope([]), ())
        self.assertEqual(_lower_envelope([(4, 2), (4, -3), (4, 5)]),
                         ((Fraction(4), Fraction(-3), None),))

    def test_random_hulls_against_every_pairwise_crossing(self):
        rng = random.Random(610092)
        checked = 0
        for _ in range(120):
            lines = [(Fraction(rng.randrange(-9, 10), rng.randrange(1, 6)),
                      Fraction(rng.randrange(-12, 13), rng.randrange(1, 6)))
                     for _ in range(rng.randrange(1, 17))]
            hull = _lower_envelope(lines)
            crossings = set()
            for i, (m, c) in enumerate(lines):
                for n, d in lines[i + 1:]:
                    if m != n:
                        crossings.add((d - c) / (m - n))
            points = sorted(crossings)
            if points:
                points += [points[0] - 1, points[-1] + 1]
                points += [(left + right) / 2 for left, right
                           in zip(sorted(crossings), sorted(crossings)[1:])]
            else:
                points = [Fraction(-3), Fraction(0), Fraction(7)]
            for point in points:
                self.assertEqual(hull_value(hull, point),
                                 min(m * point + c for m, c in lines))
                checked += 1
            self.assertTrue(all(hull[i - 1][0] > hull[i][0]
                                for i in range(1, len(hull))))
            self.assertTrue(all(hull[i - 1][2] < hull[i][2]
                                for i in range(2, len(hull))))
        self.assertGreater(checked, 5000)

    def test_section_empty_point_interval_and_affine_normalization(self):
        self.assertIsNone(_unit_section([(1, -1, 0), (0, 1, -1)], lambda: None))
        self.assertIsNone(_unit_section([(1, -2, 0), (0, 1, -2)], lambda: None))
        a, b, lower, upper = _unit_section([(1, 0, 0), (0, 1, -1)], lambda: None)
        self.assertEqual(lower, upper)
        self.assertEqual(tuple(x + lower * y for x, y in zip(a, b)), (1, 0, 0))
        a, b, lower, upper = _unit_section([(2, 1, 0), (0, 1, 2)], lambda: None)
        self.assertEqual(sum(a), 1)
        self.assertEqual(sum(b), 0)
        self.assertLess(lower, upper)
        for point in (lower, upper, (lower + upper) / 2):
            self.assertTrue(all(x + point * y >= 0 for x, y in zip(a, b)))

    def test_degenerate_plan_does_not_form_any_hulls(self):
        for basis, dimension in [([], -1), ([(1, -1)], -1),
                                  ([(2, 3)], 0),
                                  ([(1, 0, 0), (0, 1, -1)], 0)]:
            fake = SimpleNamespace(basis=basis)
            with patch('fastunknot.sector_envelope._lower_envelope',
                       side_effect=AssertionError('unexpected hull')):
                plan = sector_envelope_plan(fake)
            self.assertEqual(plan['section_dimension'], dimension)

    def test_union_of_multiple_vertex_minimum_changes(self):
        fake = SimpleNamespace(
            basis=((1, 0), (0, 1)), groups=((0, 1, 2), (3, 4)),
            potentials={0: (0, 6), 1: (1, 3), 2: (3, 1),
                        3: (0, 0), 4: (3, -1)},
            prepared={'vertex_roots': [0, 0, 0, 3, 3]})
        stats = {}
        plan = sector_envelope_plan(fake, stats=stats)
        self.assertEqual(plan['parameters'],
                         (Fraction(0), Fraction(1, 4), Fraction(1, 2),
                          Fraction(3, 4), Fraction(1)))
        self.assertEqual(stats['output_bound'], 5)
        self.assertEqual(plan['groups'][0]['corners'], (0, 1, 2))
        self.assertEqual(plan['groups'][1]['corners'], (3, 4))

    def test_endpoint_only_ties_do_not_add_pieces_or_rays(self):
        fake = SimpleNamespace(basis=((1, 0), (0, 1)), groups=((0, 1, 2),),
            potentials={0: (0, 1), 1: (0, 0), 2: (1, 0)},
            prepared={'vertex_roots': [0, 0, 0]})
        plan = sector_envelope_plan(fake)
        self.assertEqual(plan['parameters'], (Fraction(0), Fraction(1)))
        self.assertEqual(plan['groups'][0]['corners'], (1,))
        self.assertEqual(plan['groups'][0]['breakpoints'], ())


class SectorEnvelopeGeometryTests(unittest.TestCase):
    def test_genuine_interior_ray_is_an_essential_disc_beyond_q_rays(self):
        raw = attach_ball(solid_torus())
        kernel = build_sector_kernel(raw, [(0, 2), (1, 1)])
        plan = sector_envelope_plan(kernel)
        self.assertEqual(plan['parameters'], (Fraction(0), Fraction(1, 2), Fraction(1)))
        standard = list(sector_envelope_rays(kernel))
        quad = list(sector_rays(kernel, phase='quadrilateral'))
        extra = [surface for surface in standard if surface not in quad]
        self.assertEqual(len(standard), 3)
        self.assertEqual(extra, [
            [[1, 1, 0, 0, 0, 0, 1], [0, 2, 0, 0, 0, 1, 0]],
        ])
        result = normal_compressing_disk_count(raw, extra[0], record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['compressing_disk_components'], 1)
        self.assertTrue(verify_normal_disk_count_certificate(raw, extra[0],
                                                            result['certificate']))

    def test_all_small_ball_extension_sectors_against_dense_reference(self):
        raw = solid_torus()
        checks = 0
        for count in (1, 2, 3):
            for choices in product((-1, 0, 1, 2), repeat=count):
                allowed = [(i, typ) for i, typ in enumerate(choices) if typ >= 0]
                kernel = build_sector_kernel(raw, allowed)
                if len(kernel.basis) > 2:
                    continue
                stats = {}
                actual = vectors(sector_envelope_rays(kernel, stats=stats))
                reference = dense_reference_rays(dense_sector_model(raw, allowed),
                                                'standard')
                expected = vectors(value[0] for value in reference.values())
                with self.subTest(count=count, allowed=allowed):
                    self.assertEqual(actual, expected)
                    self.assertEqual(actual, vectors(sector_rays(
                        kernel, phase='standard', method='arrangement')))
                    self.assertEqual(stats['emitted_rays'], len(actual))
                    self.assertEqual(stats['bases_attempted'], len(actual))
                    self.assertLessEqual(len(actual), stats['output_bound'])
                    self.assertLessEqual(stats['output_bound'], 4 * len(allowed) + 2)
                checks += 1
            raw = attach_ball(raw)
        self.assertGreater(checks, 50)

    def test_high_precision_projection_and_plan_piece_values(self):
        kernel = build_sector_kernel(attach_ball(solid_torus()), [(0, 2), (1, 0)])
        self.assertEqual(len(kernel.basis), 2)
        # A rational basis change changes neither feasible rays nor surfaces.
        original = vectors(sector_envelope_rays(kernel))
        u, v = kernel.basis
        denominator = 2 ** 257 + 7
        kernel.basis = (tuple(x + Fraction(y, denominator) for x, y in zip(u, v)),
                        tuple(x + Fraction(2 * y, denominator) for x, y in zip(u, v)))
        plan = sector_envelope_plan(kernel)
        self.assertEqual(original, vectors(sector_envelope_rays(kernel)))
        self.assertEqual(plan['section_dimension'], 1)
        for group, recorded in zip(kernel.groups, plan['groups']):
            points = (plan['lower'],) + recorded['breakpoints'] + (plan['upper'],)
            for corner, left, right in zip(recorded['corners'], points, points[1:]):
                sample = (left + right) / 2
                intercept, slope = plan['projected_potentials'][corner]
                value = intercept + sample * slope
                self.assertEqual(value, min(c + sample * m for i, (c, m)
                    in plan['projected_potentials'].items() if i in group))

    def test_projected_lifts_avoid_old_hyperplanes_rank_and_lift(self):
        kernel = build_sector_kernel(attach_ball(solid_torus()), [(0, 2), (1, 0)])
        with patch('fastunknot.normal_sector._hyperplanes',
                   side_effect=AssertionError('quadratic hyperplane construction')):
            with patch.object(kernel, 'is_standard_ray',
                              side_effect=AssertionError('rank test')):
                with patch.object(kernel, 'lift',
                                  side_effect=AssertionError('repeated projection')):
                    stats = {}
                    rays = list(sector_envelope_rays(kernel, stats=stats))
        self.assertEqual(len(rays), 2)
        self.assertEqual(stats['projected_lifts'], 2)
        self.assertEqual(stats['potential_projections'], 2 * len(kernel.classes))

    def test_exact_cap_and_inconclusive_partial_iteration(self):
        kernel = build_sector_kernel(attach_ball(solid_torus()), [(0, 2), (1, 0)])
        rays = list(sector_envelope_rays(kernel))
        self.assertEqual(len(rays), 2)
        for limit in (0, 1):
            stats = {}
            seen = []
            with self.assertRaises(SearchLimit):
                for ray in sector_envelope_rays(kernel, max_bases=limit, stats=stats):
                    seen.append(ray)
            self.assertEqual(len(seen), limit)
            self.assertEqual(stats['bases_attempted'], limit)
            self.assertEqual(stats['emitted_rays'], limit)
        self.assertEqual(vectors(sector_envelope_rays(kernel, max_bases=2)), vectors(rays))
        for bad in (-1, True, 1.0):
            with self.assertRaises(ValueError):
                list(sector_envelope_rays(kernel, max_bases=bad))

    def test_empty_cap_zero_and_higher_dimension_rejected(self):
        empty = build_sector_kernel(solid_torus(), [])
        self.assertEqual(list(sector_envelope_rays(empty, max_bases=0)), [])
        fake = SimpleNamespace(basis=((), (), ()))
        with self.assertRaises(ValueError):
            list(sector_envelope_rays(fake))

    def test_false_valued_callback_cancellation_propagates(self):
        class Cancel:
            def __init__(self):
                self.calls = 0

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == 7:
                    raise RuntimeError('cancel envelope')

        kernel = build_sector_kernel(attach_ball(solid_torus()), [(0, 2), (1, 0)])
        with self.assertRaisesRegex(RuntimeError, 'cancel envelope'):
            list(sector_envelope_rays(kernel, check=Cancel()))


if __name__ == '__main__':
    unittest.main()
