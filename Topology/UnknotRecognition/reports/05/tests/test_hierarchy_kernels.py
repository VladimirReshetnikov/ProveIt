from dataclasses import replace
import unittest

from unknot_recognition.accounting import (HierarchyBound, numerical_cheeger_inequality,
                                           pattern_complexity)
from unknot_recognition.normal import SimplicialTriangulation, solid_torus_example
from unknot_recognition.pattern import SphericalPattern

K4 = [[0, 2, 1], [0, 3, 4], [3, 1, 5], [5, 2, 4]]
CUBE = [[0, 2, 1], [0, 3, 4], [3, 5, 6], [5, 1, 7],
        [8, 2, 9], [7, 8, 10], [11, 6, 10], [9, 4, 11]]
PRISM = [[0, 1, 2], [0, 3, 4], [3, 2, 5], [7, 1, 6], [6, 4, 8], [5, 7, 8]]


class PatternTests(unittest.TestCase):
    def test_empty_and_circle(self):
        self.assertTrue(SphericalPattern([]).classify().essential)
        self.assertTrue(SphericalPattern([], 1).classify().essential)

    def test_disconnected(self):
        for p in (SphericalPattern([], 2), SphericalPattern(K4, 1),
                  SphericalPattern(K4 + [[x + 6 for x in row] for row in K4])):
            r = p.classify()
            self.assertFalse(r.essential)
            self.assertTrue(p.verify_witness(r))
            self.assertEqual(r.cut_edges, ())

    def test_theta_k4_cube(self):
        for p in (SphericalPattern([[0, 1, 2], [0, 2, 1]]),
                  SphericalPattern(K4), SphericalPattern(CUBE)):
            self.assertTrue(p.classify().essential)

    def test_bridge(self):
        p = SphericalPattern([[0, 0, 1], [1, 2, 2]])
        r = p.classify()
        self.assertFalse(r.essential)
        self.assertEqual(r.cut_edges, (1,))
        self.assertTrue(p.verify_witness(r))

    def test_nontrivial_three_bond(self):
        p = SphericalPattern(PRISM)
        r = p.classify()
        self.assertFalse(r.essential)
        self.assertEqual(len(r.cut_edges), 3)
        self.assertEqual(len(r.side_vertices), 3)
        self.assertTrue(p.verify_witness(r))

    def test_forged_witness(self):
        p = SphericalPattern(PRISM)
        r = p.classify()
        self.assertFalse(p.verify_witness(replace(r, dual_faces=(0, 0, 0, 0))))
        self.assertFalse(p.verify_witness(replace(r, cut_edges=(99,))))
        self.assertFalse(p.verify_witness(replace(r, side_vertices=(0,))))

    def test_invalid_rotation(self):
        for rotation in ([[0, 1, 2], [0, 1, 2]], [[0, 0]], [[1, 1, 2]],
                         [[0, 1, 2], [0, 2, True]]):
            with self.assertRaises(ValueError):
                SphericalPattern(rotation)


class NormalTests(unittest.TestCase):
    def test_ball(self):
        t = SimplicialTriangulation([(0, 1, 2, 3)])
        self.assertEqual(t.cocycle_basis(), ())
        zero = t.normal_from_cocycle([0] * 6)
        self.assertEqual(t.normal_summary(zero)['disks'], 0)

    def test_solid_torus(self):
        for m in (3, 4, 6):
            t = solid_torus_example(m)
            basis = t.cocycle_basis()
            self.assertEqual(len(basis), 1)
            coords = t.normal_from_cocycle(basis[0])
            summary = t.normal_summary(coords)
            self.assertEqual(summary['euler_characteristic'], 1)
            self.assertEqual(summary['connectedness'], 'not computed')

    def test_huge_compressed_coordinates(self):
        t = solid_torus_example()
        scale = 1 << 400
        c = tuple(scale * x for x in t.cocycle_basis()[0])
        s = t.normal_summary(t.normal_from_cocycle(c))
        self.assertEqual(s['disks'], 3 * scale)
        self.assertEqual(s['euler_characteristic'], scale)
        self.assertLess(s['coordinate_bits'], 2000)
        self.assertEqual(s['connectedness'], 'not computed')

    def test_coboundary_triangle_level(self):
        t = SimplicialTriangulation([(0, 1, 2, 3)])
        heights = [0, 1, 2, 3]
        c = [heights[b] - heights[a] for a, b in t.edges]
        coords = t.normal_from_cocycle(c)
        self.assertEqual(sum(coords[0]), 3)
        self.assertEqual(t.normal_summary(coords)['euler_characteristic'], 3)

    def test_sign_reversal(self):
        t = solid_torus_example()
        c = t.cocycle_basis()[0]
        self.assertEqual(t.normal_from_cocycle(c), t.normal_from_cocycle([-x for x in c]))

    def test_matching_rejects_mutation(self):
        t = solid_torus_example()
        coords = [list(row) for row in t.normal_from_cocycle(t.cocycle_basis()[0])]
        coords[0][0] += 1
        with self.assertRaises(ValueError):
            t.normal_summary(coords)

    def test_quadrilateral_constraint(self):
        t = SimplicialTriangulation([(0, 1, 2, 3)])
        with self.assertRaises(ValueError):
            t.normal_summary([[0, 0, 0, 0, 1, 1, 0]])

    def test_reject_non_cocycle(self):
        t = solid_torus_example()
        c = [0] * len(t.edges)
        c[0] = 1
        with self.assertRaises(ValueError):
            t.normal_from_cocycle(c)

    def test_reject_non_manifolds(self):
        for tetrahedra in ([], [(0, 1, 2, 2)], [(0, 1, 2, 3)] * 2,
                            [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5)],
                            [(0, 1, 2, 3), (0, 4, 5, 6)],
                            [(0, 1, 2, 3), (4, 5, 6, 7)]):
            with self.subTest(tetrahedra=tetrahedra), self.assertRaises(ValueError):
                SimplicialTriangulation(tetrahedra)


class AccountingTests(unittest.TestCase):
    def test_pattern_complexity(self):
        self.assertEqual(pattern_complexity(-2, 3), 11)

    def test_base_g_plus_one(self):
        b = HierarchyBound(2, 2)
        self.assertEqual(b.potential((1, 0)), 3)
        self.assertEqual(b.potential((0, 2)), 2)
        self.assertTrue(b.verify_rebuild((1, 0), (0, 2), 0))
        self.assertEqual(b.iteration_bound(), 18)

    def test_zero_padding(self):
        b = HierarchyBound(5, 3)
        self.assertEqual(b.potential((2,)), b.potential((2, 0, 0)))

    def test_invalid_progress(self):
        b = HierarchyBound(5, 3)
        with self.assertRaises(ValueError):
            b.verify_rebuild((2, 1, 0), (2, 1, 0), 1)
        with self.assertRaises(ValueError):
            b.verify_rebuild((2, 1, 0), (1, 0, 0), 1)
        with self.assertRaises(ValueError):
            b.potential((6,))
        with self.assertRaises(ValueError):
            b.potential((1, 2, 3, 4))

    def test_cheeger_numeric_only(self):
        self.assertTrue(numerical_cheeger_inequality(1, 3, 6))
        self.assertFalse(numerical_cheeger_inequality(2, 3, 6))
        with self.assertRaises(ValueError):
            numerical_cheeger_inequality(1, 7, 6)


if __name__ == '__main__':
    unittest.main()
