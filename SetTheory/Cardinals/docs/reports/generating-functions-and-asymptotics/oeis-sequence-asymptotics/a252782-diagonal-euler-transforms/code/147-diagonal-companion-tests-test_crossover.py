from fractions import Fraction as F
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import crossover as cr
import diagonal_euler as de


class CrossoverAlgebraTests(unittest.TestCase):
    def test_all_certificate_ingredients(self):
        self.assertEqual(cr.exact_crossover_certificate()["conclusions"],
                         ["2 < delta < 3", "eta > 3"])

    def test_h_coefficient_independent_methods(self):
        self.assertEqual(tuple(cr.h_coefficient(k) for k in range(41)), cr.h_coefficients(40))
        self.assertEqual(cr.h_coefficients(6),
                         (F(1), F(1), F(3, 2), F(7, 6), F(25, 24), F(27, 40), F(331, 720)))

    def test_psi_residue_initial_terms(self):
        self.assertEqual(cr.psi_coefficients(0, 2), (F(1), F(7, 6), F(331, 720)))
        self.assertEqual(cr.psi_coefficients(1, 2), (F(1), F(9, 20), F(1979, 20160)))
        self.assertEqual(cr.psi_coefficients(2, 2), (F(1), F(25, 24), F(1303, 5040)))

    def test_symbolic_q_e_identities_all_h(self):
        # Equality of coefficient arrays is an exact polynomial identity in h.
        for r in range(3):
            self.assertEqual(cr.derived_q_e_polynomials(r),
                             (cr.Q_POLYNOMIALS[r], cr.E_POLYNOMIALS[r]))

    def test_p_factor_all_cutoff_cases(self):
        for m in range(1, 13):
            for ell in range(20):
                p = cr.p_factor(m, ell)
                self.assertGreaterEqual(p, 0)
                self.assertLessEqual(p, 1)
                self.assertEqual(p, cr.polynomial_value(cr.p_inverse_m_polynomial(ell), F(1, m)))
                if ell > m:
                    self.assertEqual(p, 0)
        self.assertEqual(cr.p_factor(1, 0), 1)
        self.assertEqual(cr.p_factor(1, 1), 1)
        self.assertEqual(cr.p_factor(1, 2), 0)

    def test_p_first_two_coefficients(self):
        for ell in range(41):
            p = cr.p_inverse_m_polynomial(ell)
            p += (F(0),) * max(0, 3 - len(p))
            self.assertEqual(p[0], 1)
            self.assertEqual(p[1], -F(ell * (ell - 1), 2))
            self.assertEqual(p[2], F(ell * (ell - 1) * (ell - 2) * (3 * ell - 1), 24))

    def test_operator_coefficients_act_on_monomials(self):
        for r in range(3):
            for h in range(12):
                ell = 2 * h + int(r == 1)
                self.assertEqual(cr.polynomial_value(cr.Q_POLYNOMIALS[r], h), F(ell * (ell - 1), 2))
                self.assertEqual(cr.polynomial_value(cr.E_POLYNOMIALS[r], h),
                                 F(ell * (ell - 1) * (ell - 2) * (3 * ell - 1), 24))

    def test_cleared_exponent_inequalities(self):
        inequalities = cr.rational_exponent_inequalities()
        self.assertEqual(inequalities["delta_upper"], (F(512, 729), F(25, 32)))
        self.assertEqual(inequalities["delta_lower"], (F(25, 32), F(64, 81)))
        self.assertEqual(inequalities["eta_lower"], (F(9, 16), F(512, 729)))
        for left, right in inequalities.values():
            self.assertLess(left, right)
            self.assertIs(type(left), F)
            self.assertIs(type(right), F)

    def test_non_diagonal_integer_exponent_cases(self):
        for degree, exponent in ((0, 7), (9, 0), (13, 2), (12, 7), (10, 20), (7, 31)):
            for sign in (1, -1):
                row = de.euler_row(exponent, degree, sign)
                self.assertEqual(row, de.direct_product_row(exponent, degree, sign))
                self.assertEqual(row, de.logarithmic_atom_row(exponent, degree, sign))

    def test_invalid_crossover_arguments(self):
        for func, args in ((cr.h_coefficient, (-1,)), (cr.h_coefficients, (-1,)),
                           (cr.psi_coefficients, (3, 2)), (cr.p_factor, (0, 1)),
                           (cr.p_inverse_m_polynomial, (-1,))):
            with self.assertRaises(ValueError):
                func(*args)
        for func, args in ((cr.h_coefficient, (1.0,)), (cr.h_coefficients, (True,)),
                           (cr.psi_coefficients, (1, F(2))), (cr.p_factor, (2, False)),
                           (cr.polynomial_multiply, ([], (F(1),))),
                           (cr.polynomial_multiply, ((0.5,), (1,))),
                           (cr.polynomial_value, ((1, 2), 0.5))):
            with self.assertRaises(TypeError):
                func(*args)


if __name__ == '__main__':
    unittest.main()
