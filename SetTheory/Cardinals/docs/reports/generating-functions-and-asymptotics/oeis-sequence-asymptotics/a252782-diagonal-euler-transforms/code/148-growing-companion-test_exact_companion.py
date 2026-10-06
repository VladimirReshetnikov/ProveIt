"""Exact finite regression checks for Report148; effective under python -O."""
from fractions import Fraction as Q
from math import factorial
import json
from pathlib import Path
import tempfile
import unittest

import exact_companion as ec


class EulerProductTests(unittest.TestCase):
    def test_integer_frozen_rows_against_independent_binomial_profiles(self):
        for epsilon in (-1, 1):
            for t in (0, 1, 2, 3, 5, 8):
                with self.subTest(epsilon=epsilon, t=t):
                    weights = ec.integer_weights(32, t)
                    recurrence = ec.divisor_recurrence(weights, epsilon)
                    self.assertEqual(recurrence, ec.profile_convolution(weights, epsilon))
                    self.assertTrue(all(c.denominator == 1 and c >= 0 for c in recurrence))
        # t=0 is an extra algebraic control, outside the theorem's positive-t range.

    def test_known_small_semantic_rows(self):
        self.assertEqual(ec.divisor_recurrence(ec.integer_weights(6, 1), 1),
                         list(map(Q, (1, 1, 3, 6, 13, 24, 48))))
        self.assertEqual(ec.divisor_recurrence(ec.integer_weights(5, 1), -1),
                         list(map(Q, (1, 1, 2, 5, 8, 16))))
        self.assertEqual(ec.factor_coefficients(Q(3), -1, 5), list(map(Q, (1, 3, 3, 1, 0, 0))))
        self.assertEqual(ec.factor_coefficients(Q(3), 1, 4), list(map(Q, (1, 3, 6, 10, 15))))

    def test_frozen_exponent_negative_fixture(self):
        for epsilon in (-1, 1):
            with self.subTest(epsilon=epsilon):
                correct = ec.divisor_recurrence(ec.integer_weights(6, 6), epsilon)[6]
                self.assertEqual(correct, ec.profile_convolution(ec.integer_weights(6, 6), epsilon)[6])
                self.assertNotEqual(correct, ec.wrong_diagonal_recurrence(6, epsilon)[6])

    def test_rational_weight_generalization_both_signs(self):
        # These are exact formal surrogates, not alleged values j^t at one real t.
        for offset in (1, 2, 5):
            weights = [Q(0)] + [Q(j + offset, j + 1) for j in range(1, 25)]
            for epsilon in (-1, 1):
                with self.subTest(offset=offset, epsilon=epsilon):
                    self.assertEqual(ec.divisor_recurrence(weights, epsilon),
                                     ec.profile_convolution(weights, epsilon))

    def test_signed_factor_requires_no_false_positivity(self):
        weights = [Q(0)] * 9
        weights[2] = Q(3, 2)
        expected = [Q(1), Q(0), Q(3, 2), Q(0), Q(3, 8), Q(0), Q(-1, 16), Q(0), Q(3, 128)]
        self.assertEqual(ec.divisor_recurrence(weights, -1), expected)
        self.assertEqual(ec.profile_convolution(weights, -1), expected)
        self.assertLess(expected[6], 0)

    def test_exact_core_removal_and_normalized_log_atom_identity(self):
        for cube_root_m in (1, 2):
            m = cube_root_m ** 3
            for t in (3, 6):
                x0 = Q(cube_root_m, 3 ** (t // 3))
                a = 2 ** t * x0 ** 2
                self.assertEqual(x0 ** 3, Q(m, 3 ** t))
                self.assertEqual(a ** 3, m * m * Q(8, 9) ** t)
                base = Q(3 ** (m * t), factorial(m))
                normalizers = (base,
                               Q(3, 2) * Q(4 ** t * 3 ** ((m - 1) * t), factorial(m - 1)),
                               2 ** t * base)
                for r in range(3):
                    self.assertEqual(x0 ** r * normalizers[r] / base,
                                     ec.NORMALIZERS[r] * a ** ec.RESIDUES[r])
                    for epsilon in (-1, 1):
                        n = 3 * m + r
                        lhs = ec.divisor_recurrence(ec.integer_weights(n, t), epsilon)[n] / base * x0 ** r
                        rhs = ec.normalized_log_atom_profile(m, r, t, x0, epsilon)
                        self.assertEqual(lhs, rhs, (m, r, t, epsilon))

    def test_guard_does_not_disappear_under_optimization(self):
        with self.assertRaisesRegex(ValueError, "active"):
            ec.require(False, "active")
        with self.assertRaises(ValueError):
            ec.divisor_recurrence([Q(0), Q(1)], 0)


class ResidueAndPureCloudTests(unittest.TestCase):
    def test_h_recurrence_and_factorial_profiles(self):
        self.assertEqual(ec.h_by_recurrence(60), [ec.h_by_profiles(k) for k in range(61)])
        self.assertEqual(ec.h_by_recurrence(2), [Q(1), Q(1), Q(3, 2)])

    def test_residue_map_leading_normalizer_and_single_five(self):
        self.assertEqual(ec.RESIDUES, (0, 2, 1))
        self.assertEqual(ec.NORMALIZERS, (Q(1), Q(3, 2), Q(1)))
        self.assertEqual(tuple(ec.h_by_profiles(q) for q in ec.RESIDUES), ec.NORMALIZERS)
        for r, q in enumerate(ec.RESIDUES):
            self.assertEqual((2 * q) % 3, r)
            self.assertEqual((2 * q - r) // 3, (0, 1, 0)[r])
            shifted = (q + 2) % 3
            self.assertEqual((5 + 2 * shifted) % 3, r)
            self.assertEqual((5 + 2 * shifted - r) // 3, (3, 2, 1)[r])
            for k in range(100):
                self.assertEqual((2 * k) % 3 == r, k % 3 == q)
                self.assertEqual((5 + 2 * k) % 3 == r, k % 3 == shifted)

    def test_exact_pure_cloud_polynomial_numerators(self):
        for m in range(1, 21):
            for r in range(3):
                with self.subTest(m=m, r=r):
                    profiles = ec.pure_profile_coefficients(m, r)
                    filtered = ec.pure_filtered_coefficients(m, r)
                    self.assertEqual(profiles, filtered)
                    q = ec.RESIDUES[r]
                    self.assertEqual(filtered[q], ec.NORMALIZERS[r])
        # These are finite numerators. F_q itself remains an infinite entire series.

    def test_pure_cloud_polynomial_moments_and_log_coefficients(self):
        a = ec.X
        for r in range(3):
            values = ec.pure_polynomial_identities(r)
            self.assertEqual(values["mean_X"], (2 * a - r) / 3)
            self.assertEqual(values["second_X"], (20 * a ** 2 + 4 * (1 - r) * a + r * r) / 9)
            expected_first = (-Q(8, 9) * a ** 4 - Q(8, 9) * a ** 3
                              + Q(4 * (r - 1), 9) * a ** 2
                              + Q(2 * r + 1, 9) * a - Q(r * (r + 3), 18))
            self.assertEqual(values["first_log_numerator"], expected_first)
            self.assertEqual(values["second_log_numerator"].terms.get((6, 0)), Q(32, 27))
            self.assertTrue(all(i <= 6 and j == 0 for i, j in values["second_log_numerator"].terms))
            self.assertEqual(Q(32, 27) + Q(1, 2) * Q(8, 9) ** 2, Q(128, 81))

    def test_exact_V_expectation_retained_coefficients(self):
        a, inv_m = ec.X, ec.W
        for r in range(3):
            d = Q(4, 3) * a ** 2
            mean = (4 * a ** 2 + 2 * a - r) / 3
            variance = (16 * a ** 2 + 4 * a) / 9
            third_cumulant = Q(8, 27) * (a + 8 * a ** 2)
            x1 = (2 * a - r) / 3
            x2 = variance + x1 ** 2
            ell3 = mean ** 3 + 3 * mean * variance + third_cumulant
            ev = (-d * x1 - x2 / 2 + (d + x1) / 2) * inv_m - ell3 * inv_m ** 2 / 6
            retained = ec.Laurent({(i, j): c for (i, j), c in ev.terms.items() if 4 * j - i < 3})
            expected = (-Q(8, 9) * a ** 3 * inv_m + Q(4 * (r - 1), 9) * a ** 2 * inv_m
                        - Q(32, 81) * a ** 6 * inv_m ** 2)
            self.assertEqual(retained, expected)
            leading_quadratic = d ** 2 * x2 * inv_m ** 2 / 2
            retained_quadratic = ec.Laurent({(i, j): c for (i, j), c in leading_quadratic.terms.items() if 4 * j - i < 3})
            self.assertEqual(retained_quadratic, Q(160, 81) * a ** 6 * inv_m ** 2)
            self.assertEqual(Q(-32, 81) + Q(160, 81), Q(128, 81))

    def test_only_small_activity_negative_degree_exception(self):
        exceptions = []
        for r, q in enumerate(ec.RESIDUES):
            for degree in range(r, 101, 3):
                if Q(degree, 2) - q < 0:
                    exceptions.append((r, degree))
        self.assertEqual(exceptions, [(1, 1)])


class FormalInverseTests(unittest.TestCase):
    def test_forward_log_changes_128_over_81_to_32_over_27(self):
        x, w, u, v = ec.X, ec.W, ec.U, ec.V
        for r in range(3):
            forward = (1 + u * (-Q(8, 9) * x ** 3)
                       + u * u * (Q(4 * (r - 1), 9) * x ** 2 + Q(128, 81) * x ** 6)
                       + v * w)
            self.assertEqual(forward.unit_log(),
                             u * (-Q(8, 9) * x ** 3)
                             + u * u * (Q(4 * (r - 1), 9) * x ** 2 + Q(32, 27) * x ** 6)
                             + v * w)

    def test_formal_inverse_and_log_parameter(self):
        x = ec.X
        for r in range(3):
            values = ec.inverse_identities(r)
            self.assertEqual(values["log_model"], ec.Series(-Q(8, 9) * x ** 4))
            log_s = values["minus_L_times_t_correction"]
            self.assertEqual(-log_s.coefficient(1, 0), Q(3, 4) * ec.monomial(-1))
            self.assertEqual(-log_s.coefficient(2, 0),
                             -Q(3 * (2 * r - 1), 16) * ec.monomial(-2) - x ** 2)
            self.assertEqual(-log_s.coefficient(0, 1), -Q(27, 32) * ec.monomial(-4, 1))
            self.assertEqual(log_s.coefficient(), 0)

    def test_affine_delta_exponents(self):
        # An exponent is encoded as (coefficient of delta, constant).
        p = (Q(1, 2), Q(5, 6))
        self.assertEqual((p[0], p[1] - Q(1, 3)), (Q(1, 2), Q(1, 2)))
        self.assertEqual((p[0], p[1] - Q(4, 3)), (Q(1, 2), Q(-1, 2)))
        # lambda5=m^-delta*a^((3delta+5)/2), a=s^(1/3)m^(1/4).
        self.assertEqual((Q(3, 2) / 3, Q(5, 2) / 3), p)
        self.assertEqual((-1 + Q(3, 2) / 4, Q(5, 2) / 4), (Q(-5, 8), Q(5, 8)))
        # The second pair is -beta=-(5/8)(delta-1).

    def test_quotient_discards_exactly_the_admissible_mixed_orders(self):
        self.assertEqual(ec.U * ec.U * ec.U, 0)
        self.assertEqual(ec.U * ec.V, 0)
        self.assertEqual(ec.V * ec.V, 0)
        self.assertNotEqual(ec.U * ec.U, 0)
        beta_lower = Q(5, 8)
        self.assertGreater(beta_lower + Q(1, 4), Q(3, 4))
        self.assertGreater(2 * beta_lower, Q(3, 4))
        self.assertGreater(beta_lower + Q(1, 2), Q(3, 4))


class RationalInequalityTests(unittest.TestCase):
    def test_exact_exponent_ordering_witnesses(self):
        for witness in ec.rational_witnesses():
            with self.subTest(name=witness["name"]):
                lhs, rhs = Q(witness["left"]), Q(witness["right"])
                if witness["relation"] == "<":
                    self.assertLess(lhs, rhs)
                    self.assertLess(witness["cleared_left"], witness["cleared_right"])
                else:
                    self.assertGreater(lhs, rhs)
                    self.assertGreater(witness["cleared_left"], witness["cleared_right"])
        self.assertEqual(25 ** 5 * 9 ** 11, 306455660244140625)
        self.assertEqual(32 ** 5 * 8 ** 11, 288230376151711744)
        self.assertEqual(Q(5, 8) * (Q(11, 5) - 1), Q(3, 4))
        self.assertEqual(Q(5, 4) * Q(1, 2) - Q(1, 8), Q(1, 2))

    def test_global_depletion_union_bound_on_finite_domain(self):
        for m in range(1, 49):
            for ell in range(2 * m + 9):
                p = ec.falling_ratio(m, ell)
                self.assertGreaterEqual(p, 0)
                self.assertLessEqual(p, 1)
                self.assertGreaterEqual(1 - p, 0)
                self.assertLessEqual(1 - p, Q(ell * (ell - 1), 2 * m))
                if ell > m:
                    self.assertEqual(p, 0)

    def test_global_second_order_approximation_on_finite_domain(self):
        checked = 0
        for m in range(1, 49):
            for ell in range(2 * m + 9):
                self.assertTrue(ec.falling_global_bound_check(m, ell), (m, ell))
                checked += 1
        self.assertEqual(checked, 2784)

    def test_rational_auxiliary_bounds_cover_both_global_branches(self):
        # These are also finite probes, with the symbolic branch argument in README.
        for m in range(1, 49):
            for ell in range(2, 2 * m + 9):
                y = Q(ell * (ell - 1) * (2 * ell - 1), 12 * m * m)
                self.assertLessEqual(y, Q(ell ** 3, 6 * m * m))
                if 2 * ell <= m:
                    remainder_bound = sum((Q(i, m) ** 3 / (3 * (1 - Q(i, m))) for i in range(ell)), Q(0))
                    self.assertLessEqual(remainder_bound, Q(ell ** 4, 6 * m ** 3))
                    self.assertLessEqual(y * y / 2, Q(ell ** 6, 72 * m ** 4))
                else:
                    self.assertLessEqual(2 + y, 9 * Q(ell ** 4, m ** 3))

    def test_rational_exponential_enclosures(self):
        for x in (Q(0), Q(1, 10), Q(1, 2), Q(1), Q(3, 2), Q(4)):
            low, high = ec.exp_negative_bounds(x, terms=10)
            finer_low, finer_high = ec.exp_negative_bounds(x, terms=12)
            self.assertLessEqual(0, low)
            self.assertLessEqual(low, finer_low)
            self.assertLessEqual(finer_low, finer_high)
            self.assertLessEqual(finer_high, high)
            self.assertLessEqual(high, 1)
        self.assertEqual(ec.exp_negative_bounds(0), (Q(1), Q(1)))


class CertificateTests(unittest.TestCase):
    def test_checked_in_certificate_matches_exact_regeneration(self):
        path = Path(__file__).with_name("certificate.json")
        self.assertEqual(ec.verify_certificate(path), ec.build_certificate()["payload_sha256"])

    def test_certificate_output_is_exclusive_and_never_overwrites(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "new.json"
            ec.write_certificate_exclusive(path, {"value": 1})
            original = path.read_bytes()
            with self.assertRaises(FileExistsError):
                ec.write_certificate_exclusive(path, {"value": 2})
            self.assertEqual(path.read_bytes(), original)

    def test_certificate_output_rejects_symlink_files_and_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "target.json"
            target.write_text("untouched", encoding="utf-8")
            link = root / "linked.json"
            link.symlink_to(target)
            with self.assertRaises(OSError):
                ec.write_certificate_exclusive(link, {"overwrite": True})
            self.assertEqual(target.read_text(encoding="utf-8"), "untouched")
            dangling = root / "dangling.json"
            dangling.symlink_to(root / "must-not-create.json")
            with self.assertRaises(OSError):
                ec.write_certificate_exclusive(dangling, {})
            self.assertFalse((root / "must-not-create.json").exists())
            real_directory = root / "real"
            real_directory.mkdir()
            linked_directory = root / "alias"
            linked_directory.symlink_to(real_directory, target_is_directory=True)
            with self.assertRaises(OSError):
                ec.write_certificate_exclusive(linked_directory / "new.json", {})
            self.assertFalse((real_directory / "new.json").exists())

    def test_tampering_is_rejected(self):
        certificate = ec.build_certificate()
        certificate["payload"]["residue_map"][1] = 1
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "corrupt.json"
            path.write_text(json.dumps(certificate), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "differs"):
                ec.verify_certificate(path)


if __name__ == "__main__":
    unittest.main(verbosity=2)
