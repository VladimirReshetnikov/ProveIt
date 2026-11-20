"""Finite exact tests: meaningful regressions, not universal iPRA proofs."""
from fractions import Fraction as F
from itertools import product
import unittest

from certified_contractions import (
    AffineBox, CertificateError, GainCertificate, Q, Q_coherence_budget,
    Q_equation_budget, Q_equation_residual, add, componentwise_le,
    coupled_demo, derive_weights, dyadic, dyadic_decimal, floor_dyadic,
    matvec, neumann_supersolution, no_gap_defect, no_gap_epsilon,
    no_gap_fixed_point, no_gap_step, norm_w, scale, sub,
    tower_adjacent_comparison_bound, tower_adjacent_distance,
    tower_commutation_defect, tower_defect_budget, tower_iteration,
    tower_metric, tower_residual, tower_residual_budget, tower_step, tower_y,
)


class GainAndNeumannTests(unittest.TestCase):
    def setUp(self):
        self.model, self.root = coupled_demo()
        self.cert = self.model.gain

    def test_asymmetric_coupling_requires_weights(self):
        self.assertEqual(matvec(self.cert.A, self.cert.w), (F(2), F(1, 2)))
        self.assertEqual(self.cert.q, F(1, 2))
        with self.assertRaises(CertificateError):
            GainCertificate(self.cert.A, (F(1), F(1)), 2)

    def test_derived_weights_from_supplied_power(self):
        result = derive_weights(self.cert.A, 2, F(1, 4))
        self.assertEqual(result.power_on_ones, (F(1, 4), F(1, 4)))
        self.assertEqual(result.certificate.w, (F(3), F(9, 8)))
        self.assertEqual(result.certificate.s, 4)
        self.assertTrue(componentwise_le(
            matvec(result.certificate.A, result.certificate.w),
            scale(result.certificate.q, result.certificate.w)))

    def test_power_failure_is_rejected_without_unbounded_search(self):
        for m, theta in [(1, F(1, 2)), (2, F(1, 5))]:
            with self.subTest(m=m, theta=theta), self.assertRaises(CertificateError):
                derive_weights(self.cert.A, m, theta)
        for m, theta in [(0, F(0)), (2, F(1)), (2, F(-1, 8))]:
            with self.subTest(m=m, theta=theta), self.assertRaises(CertificateError):
                derive_weights(self.cert.A, m, theta)
        with self.assertRaises(CertificateError):
            derive_weights(((1, 0), (0, 1)), 3, F(7, 8))

    def test_s_one_and_zero_gain_boundary(self):
        cert = GainCertificate(((0, 0), (0, 0)), (1, 3), 1)
        self.assertEqual(cert.q, F(0))
        result = derive_weights(((0, 0), (0, 0)), 1, F(0))
        self.assertEqual(result.certificate.s, 1)
        rho = (F(1, 5), F(2, 7))
        self.assertTrue(componentwise_le(rho, neumann_supersolution(cert, rho, 0).z))
        self.assertEqual(neumann_supersolution(cert, rho, 1).z, rho)
        with self.assertRaises(CertificateError):
            GainCertificate(((F(1, 10),),), (1,), 1)

    def test_invalid_gain_shapes_and_numbers(self):
        invalid = [
            ((), (), 2),
            (((0, 1), (0,)), (1, 1), 2),
            (((0,),), (), 2),
            (((0,),), (0,), 2),
            (((0,),), (-1,), 2),
            (((-1,),), (1,), 2),
            (((0,),), (1,), 0),
            (((0,),), (1,), F(2)),
            (((0.0,),), (1,), 2),
            (((False,),), (1,), 2),
            (((0,),), (True,), 2),
        ]
        for A, w, s in invalid:
            with self.subTest(A=A, w=w, s=s), self.assertRaises(CertificateError):
                GainCertificate(A, w, s)

    def test_weighted_operator_estimate_on_signed_grid(self):
        values = (F(-2), F(-1, 2), F(0), F(1, 3), F(2))
        for x in product(values, repeat=2):
            self.assertLessEqual(norm_w(matvec(self.cert.A, x), self.cert.w),
                                 self.cert.q * norm_w(x, self.cert.w))

    def test_neumann_against_independent_closed_form_inverse(self):
        for rho in [(F(0), F(0)), (F(1, 100), F(1, 100)),
                    (F(2, 7), F(1, 13)), (F(0), F(5, 3))]:
            r, s = rho
            exact_solution = (F(4, 3) * (r + 2 * s), r / 6 + F(4, 3) * s)
            self.assertEqual(add(matvec(self.cert.A, exact_solution), rho), exact_solution)
            previous = None
            for N in range(13):
                with self.subTest(rho=rho, N=N):
                    data = neumann_supersolution(self.cert, rho, N)
                    self.assertTrue(componentwise_le(add(matvec(self.cert.A, data.z), rho), data.z))
                    self.assertTrue(componentwise_le(exact_solution, data.z))
                    self.assertLessEqual(norm_w(sub(data.z, exact_solution), self.cert.w),
                                         self.cert.s * self.cert.q ** N * norm_w(rho, self.cert.w))
                    if previous is not None:
                        self.assertTrue(componentwise_le(data.z, previous))
                    previous = data.z

    def test_neumann_zero_horizon_and_general_dimension(self):
        rho = (F(1, 7), F(2, 9))
        zero = neumann_supersolution(self.cert, rho, 0)
        self.assertEqual(zero.partial_sum, (F(0), F(0)))
        self.assertEqual(zero.tail, rho)
        self.assertEqual(zero.z, scale(self.cert.s * norm_w(rho, self.cert.w), self.cert.w))
        cert3 = GainCertificate(((0, F(1, 8), 0), (0, 0, F(1, 4)),
                                 (F(1, 2), 0, 0)), (1, 1, 1), 2)
        for N in range(9):
            data = neumann_supersolution(cert3, (1, 2, 3), N)
            self.assertTrue(componentwise_le(add(matvec(cert3.A, data.z), (1, 2, 3)), data.z))

    def test_invalid_neumann_inputs(self):
        for rho, N in [((1,), 2), ((-1, 2), 2), ((1, 2), -1), ((1, 2), 2.0)]:
            with self.subTest(rho=rho, N=N), self.assertRaises(CertificateError):
                neumann_supersolution(self.cert, rho, N)

    def test_affine_box_and_posteriori_residual(self):
        for x in product((F(0), F(1, 4), F(1, 2), F(3, 4), F(1)), repeat=2):
            point = (4 * x[0], x[1])
            self.assertTrue(self.model.contains(self.model.step(point)))
        self.assertEqual(self.model.step(self.root), self.root)
        for t in range(14):
            y = self.model.iterate((0, 0), t)
            error = norm_w(sub(y, self.root), self.cert.w)
            self.assertLessEqual(error, self.cert.s * self.model.residual(y))
            self.assertLessEqual(error, self.cert.q ** t * norm_w(self.root, self.cert.w))

    def test_invalid_affine_boxes_and_orbits(self):
        for b, lower, upper in [
            ((1, F(1, 4)), (0, 2), (4, 1)),
            ((10, F(1, 4)), (0, 0), (4, 1)),
            ((1,), (0, 0), (4, 1)),
        ]:
            with self.subTest(b=b, lower=lower, upper=upper), self.assertRaises(CertificateError):
                AffineBox(self.cert, b, lower, upper)
        with self.assertRaises(CertificateError):
            self.model.iterate((5, 0), 1)
        with self.assertRaises(CertificateError):
            self.model.iterate((0, 0), -1)


class TowerTests(unittest.TestCase):
    def test_directed_dyadic_rounding_boundary_cases(self):
        for x in (F(-1), F(-1, 3), F(0), F(1, 16), F(1, 3), F(1)):
            for bits in range(7):
                y = floor_dyadic(x, bits)
                self.assertLessEqual(y, x)
                self.assertLess(x - y, dyadic(bits))
                self.assertEqual(y * (1 << bits), F(int(y * (1 << bits))))
        self.assertEqual(floor_dyadic(F(-1, 3), 2), F(-1, 2))
        self.assertEqual(floor_dyadic(F(1, 4), 2), F(1, 4))

    def test_tower_box_and_weighted_half_contraction(self):
        grid = (F(0), F(1, 2), F(1))
        for n in range(1, 4):
            points = list(product(grid, repeat=n))
            for x in points:
                self.assertTrue(all(F(0) <= a <= F(1, 2) for a in tower_step(x)))
                for y in points:
                    self.assertLessEqual(tower_metric(tower_step(x), tower_step(y)),
                                         tower_metric(x, y) / 2)

    def test_rounding_error_against_exact_orbit(self):
        for n in range(1, 4):
            exact_orbit = tuple(F(0) for _ in range(n))
            steps, bits = n + 4, n + 8
            for t in range(steps + 1):
                rounded = tower_iteration(n, t, bits)
                self.assertLessEqual(tower_metric(exact_orbit, rounded), 2 * dyadic(bits))
                exact_orbit = tower_step(exact_orbit)

    def test_predetermined_residual_schedule_through_dimension_sixteen(self):
        for n in range(1, 17):
            with self.subTest(n=n):
                y = tower_y(n)
                self.assertEqual(len(y), n)
                self.assertEqual(y, tower_iteration(n, n + 4, n + 8))
                self.assertTrue(all(F(0) <= a <= F(1) for a in y))
                self.assertLessEqual(tower_residual(n), tower_residual_budget(n))
                # Every returned coordinate is exactly a multiple of the claimed dyadic unit.
                self.assertTrue(all((a * (1 << (n + 8))).denominator == 1 for a in y))

    def test_commutation_defect_is_exact_and_saturates(self):
        for n in range(1, 13):
            saturated = tuple(F(1) for _ in range(n + 1))
            self.assertEqual(tower_commutation_defect(saturated, n), tower_defect_budget(n))
            vanished = tuple(F(1) for _ in range(n)) + (F(0),)
            self.assertEqual(tower_commutation_defect(vanished, n), F(0))
        for n in range(1, 7):
            for m in range(n + 1, n + 4):
                x = tuple(F(j, m) for j in range(m))
                self.assertEqual(tower_commutation_defect(x, n),
                                 tower_defect_budget(n) * x[n])

    def test_adjacent_residual_comparison_and_loose_error_budget(self):
        for n in range(1, 16):
            with self.subTest(n=n):
                comparison = tower_adjacent_comparison_bound(n)
                self.assertLessEqual(tower_adjacent_distance(n), comparison)
                self.assertLessEqual(comparison, dyadic(n))
                scheduled_bound = 2 * (dyadic(n + 4) + dyadic(n + 5) + dyadic(n + 2))
                self.assertEqual(scheduled_bound, F(11, 16) * dyadic(n))

    def test_multilevel_restriction_coherence(self):
        for n in range(1, 11):
            for m in range(n, 17):
                distance = tower_metric(tower_y(n), tower_y(m)[:n])
                finite_budget = sum((dyadic(j) for j in range(n, m)), F(0))
                self.assertLessEqual(distance, finite_budget)
                self.assertLessEqual(distance, 2 * dyadic(n))

    def test_coordinate_name_coherence(self):
        for i in range(4):
            for k in range(11):
                for ell in range(k, 11):
                    self.assertLessEqual(abs(Q(i, k) - Q(i, ell)), Q_coherence_budget(k))

    def test_coordinate_equation_residual(self):
        # The largest dimension queried is 16, including the i+1 observation.
        for i in range(4):
            for k in range(10):
                self.assertLessEqual(Q_equation_residual(i, k), Q_equation_budget(k))
        for i in range(3):
            self.assertLessEqual(Q_equation_residual(i, 10), Q_equation_budget(10))

    def test_solver_boundary_parameters_are_not_silently_accepted(self):
        for args in [(0, 1, 1), (1, -1, 1), (1, 1, -1), (1.0, 1, 1)]:
            with self.subTest(args=args), self.assertRaises(CertificateError):
                tower_iteration(*args)
        for n in (0, -1, True, F(1), 1.0):
            with self.subTest(n=n), self.assertRaises(CertificateError):
                tower_y(n)
        for i, k in [(-1, 0), (0, -1)]:
            with self.subTest(i=i, k=k), self.assertRaises(CertificateError):
                Q(i, k)
        for x in [(), (F(-1, 8),), (F(9, 8),)]:
            with self.subTest(x=x), self.assertRaises(CertificateError):
                tower_step(x)
        with self.assertRaises(CertificateError):
            tower_commutation_defect((F(1),), 1)
        with self.assertRaises(CertificateError):
            tower_commutation_defect((F(1), F(1)), 0)

    def test_exact_dyadic_decimal_roundtrip(self):
        for value in (F(0), F(-1, 8), F(1), F(7, 16), Q(3, 10)):
            self.assertEqual(F(dyadic_decimal(value)), value)
        self.assertEqual(dyadic_decimal(F(-1, 8)), "-0.125")
        with self.assertRaises(CertificateError):
            dyadic_decimal(F(1, 3))


class MissingGapTests(unittest.TestCase):
    def test_vanishing_defect_with_alternating_exact_fixed_points(self):
        for n in range(13):
            c = no_gap_fixed_point(n)
            self.assertEqual(no_gap_step(n, c), c)
            self.assertEqual(abs(c - no_gap_fixed_point(n + 1)), F(1))
            defect = no_gap_defect(n)
            self.assertEqual(defect, no_gap_epsilon(n))
            self.assertEqual(no_gap_defect(n + 1), defect / 2)
            self.assertEqual(defect / no_gap_epsilon(n), F(1))
            for x in (F(0), F(1, 3), F(1)):
                self.assertTrue(F(0) <= no_gap_step(n, x) <= F(1))

    def test_local_contractions_have_no_uniform_gap(self):
        for n in range(13):
            epsilon = no_gap_epsilon(n)
            x, y = F(1, 7), F(5, 6)
            self.assertEqual(abs(no_gap_step(n, x) - no_gap_step(n, y)),
                             (1 - epsilon) * abs(x - y))
            self.assertLess(no_gap_epsilon(n + 1), epsilon)
        with self.assertRaises(CertificateError):
            no_gap_step(0, F(2))


if __name__ == "__main__":
    unittest.main(verbosity=2)

