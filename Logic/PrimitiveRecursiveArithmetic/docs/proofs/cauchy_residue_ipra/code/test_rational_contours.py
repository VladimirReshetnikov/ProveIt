"""Focused, exact finite validation.  Passing tests are not a formal proof."""

import unittest
from random import Random
from fractions import Fraction as Q

from rational_contours import (
    CQ, add_chains, binomial_integral, diameter, distance_to_imaginary_interval,
    dyadic, edge_chain, perimeter, pi_interval, quadrature_derivative_error_bound,
    reciprocal_derivative_lipschitz_bound, residue_example, split_edge, subdivide_triangles,
    trap_chain, triangle_bound, triangle_edges, triangles_boundary,
)


class ExactFiniteChecks(unittest.TestCase):
    def test_rounding_and_norm(self):
        for a in range(-6, 7):
            for b in range(-6, 7):
                z = CQ(Q(a, 7), Q(b, 11))
                for bits in (0, 3, 10):
                    self.assertLessEqual((z - z.rounded(bits)).norm1(), dyadic(bits))
                w = CQ(Q(b, 5), Q(a, 3))
                self.assertLessEqual((z * w).norm1(), z.norm1() * w.norm1())
                if z != CQ():
                    self.assertEqual(z * z.inv(), CQ(1))
                    self.assertLessEqual(z.inv().norm1(), Q(2) / z.norm1())
                if z != CQ() and w != CQ():
                    h = w - z
                    self.assertEqual(w.inv() - z.inv() + h / (z * z),
                                     h * h / (z * z * w))

    def test_reciprocal_interpolation_identity(self):
        generator = Random(20261115)
        for _ in range(80):
            u = CQ(Q(generator.randint(-8, 8), generator.randint(1, 9)),
                   Q(generator.randint(-8, 8), generator.randint(1, 9)))
            v = CQ(Q(generator.randint(-8, 8), generator.randint(1, 9)),
                   Q(generator.randint(-8, 8), generator.randint(1, 9)))
            t = Q(generator.randint(0, 11), 11)
            middle = (1 - t) * u + t * v
            if CQ() in (u, v, middle):
                continue
            defect = (1 - t) / u + t / v - middle.inv()
            self.assertEqual(defect, t * (1 - t) * (v - u) ** 2 / (u * v * middle))
        for n in (2, 4, 8, 16):
            average = sum((Q(j, n) * (1 - Q(j, n)) for j in range(1, n)), Q()) / n
            self.assertEqual(average, Q(n * n - 1, 6 * n * n))

    def test_affine_and_subdivision_cancellation(self):
        triangle = (CQ(), CQ(2), CQ(0, 1))
        affine = lambda z: CQ(Q(2, 3), Q(7, 5)) + CQ(Q(4, 9), Q(-1, 3)) * z
        for depth in range(5):
            small = subdivide_triangles([triangle], depth)
            boundary = [edge for big in triangle_edges(triangle) for edge in split_edge(big, depth)]
            self.assertEqual(len(small), 4 ** depth)
            self.assertEqual(triangles_boundary(small), edge_chain(boundary))
            self.assertEqual(trap_chain(affine, triangle_edges(triangle), depth), CQ())
            for child in small:
                self.assertEqual(diameter(child), diameter(triangle) * dyadic(depth))
                self.assertEqual(perimeter(triangle_edges(child)),
                                 perimeter(triangle_edges(triangle)) * dyadic(depth))

    def test_polynomial_finite_ud_and_bound(self):
        triangle = (CQ(), CQ(2), CQ(0, 1))
        f = lambda z: z * z
        derivative = lambda z: 2 * z
        coarse = trap_chain(f, triangle_edges(triangle))
        for k in range(3):
            depth, bits = k + 2, 4
            small = subdivide_triangles([triangle], depth)
            self.assertLessEqual(diameter(triangle) * dyadic(depth), dyadic(k))
            for child in small:
                anchor = child[0]
                for z in child:
                    h = z - anchor
                    remainder = f(z).rounded(bits) - f(anchor).rounded(bits)
                    remainder -= derivative(anchor).rounded(bits) * h
                    self.assertLessEqual(remainder.norm1(),
                                         dyadic(k) * h.norm1() + dyadic(bits) * (2 + h.norm1()))
            global_sum = trap_chain(f, triangle_edges(triangle), depth, bits)
            local_sum = sum((trap_chain(f, triangle_edges(child), bits=bits) for child in small), CQ())
            self.assertEqual(global_sum, local_sum)
            self.assertLessEqual(global_sum.norm1(), triangle_bound(triangle, depth, k, bits))
            self.assertEqual(trap_chain(f, triangle_edges(triangle), depth), coarse * dyadic(2 * depth))

    def test_positive_pi_recurrence(self):
        integral = Q(1)
        for j in range(18):
            if j:
                integral *= Q(2 * j, 2 * j + 1)
            self.assertEqual(integral, binomial_integral(j))
            self.assertGreater(integral, 0)
        lo, hi = pi_interval(24)
        self.assertLess(lo, hi)
        self.assertEqual(hi - lo, 4 * dyadic(24))
        self.assertGreater(lo, Q(314159, 100000))
        self.assertLess(hi, Q(314160, 100000))

    def test_punctured_grid_boundary(self):
        _, _, triangles, outer, holes = residue_example()
        expected = add_chains(edge_chain(outer), *(edge_chain(hole, -1) for hole in holes))
        self.assertEqual(triangles_boundary(triangles), expected)
        self.assertEqual(len(triangles), 26)
        # Each oriented triangle is positive by an exact determinant test.
        for a, b, c in triangles:
            u, v = b - a, c - a
            self.assertGreater(u.re * v.im - u.im * v.re, 0)

    def test_residue_quadratures(self):
        f, poles, _, outer, holes = residue_example()
        pi_lo, pi_hi = pi_interval(24)
        for edges, multiplier in [(outer, 6), (holes[0], 2), (holes[1], 4)]:
            lipschitz = reciprocal_derivative_lipschitz_bound(edges, poles)
            previous_error = None
            for depth in (5, 7, 9):
                value = trap_chain(f, edges, depth, bits=32)
                error = quadrature_derivative_error_bound(edges, lipschitz, depth, 32)
                self.assertLessEqual(distance_to_imaginary_interval(value, multiplier * pi_lo,
                                                                    multiplier * pi_hi), error)
                if previous_error is not None:
                    self.assertLess(error, previous_error)
                previous_error = error


if __name__ == "__main__":
    unittest.main(verbosity=2)

