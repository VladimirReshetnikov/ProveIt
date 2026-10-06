#!/usr/bin/env python3
"""Opt-in standard-library symbolic regression tests; valid under python -O."""
from fractions import Fraction as F
import sys
import unittest

import symbolic_coefficients as S


class FieldTests(unittest.TestCase):
    def test_arithmetic(self):
        x, y = S.Q2(F(2, 3), F(-1, 5)), S.Q2(F(7, 2), F(3, 7))
        self.assertEqual(S.SQRT2**2, S.Q2(2))
        self.assertEqual((x + y) - y, x)
        self.assertEqual((x * y) / y, x)
        self.assertEqual(x * x.inverse(), S.ONE)
        self.assertEqual(S.SQRT2**(-2), S.Q2(F(1, 2)))
        self.assertEqual(2 / S.SQRT2, S.SQRT2)
        self.assertEqual(S.ZERO**0, S.ONE)
        self.assertFalse(S.ZERO)
        with self.assertRaises(ZeroDivisionError):
            S.ZERO.inverse()
        for value in (True, False, 1.0, "1"):
            with self.assertRaises(TypeError):
                S.Q2(value)
            with self.assertRaises(TypeError):
                S.ONE**value

    def test_gaussian_moments(self):
        self.assertEqual(S.gaussian_moment(0), S.ONE)
        self.assertEqual(S.gaussian_moment(2), S.Q2(0, F(-1, 4)))
        self.assertEqual(S.gaussian_moment(4), S.Q2(F(3, 8)))
        for power in range(1, 20, 2):
            self.assertEqual(S.gaussian_moment(power), S.ZERO)
        for m in range(1, 20):
            self.assertEqual(S.gaussian_moment(2 * m),
                             -F(2 * m - 1, 2) / S.SQRT2 * S.gaussian_moment(2 * m - 2))


class CoefficientTests(unittest.TestCase):
    def test_local_amplitude(self):
        self.assertEqual(S.local_amplitude(4), [F(1), F(-1, 4), F(7, 32),
                                                F(-47, 384), F(1361, 6144)])

    def test_displayed_four_corrections_from_both_routes(self):
        self.assertEqual(S.gaussian_coefficients(4)["coefficients"], S.DISPLAYED)
        self.assertEqual(S.discrete_ode_coefficients(4)["coefficients"], S.DISPLAYED)

    def test_all_bounded_orders_and_truncation_consistency(self):
        full = S.gaussian_coefficients(S.MAX_ORDER)
        self.assertEqual(full["odd_moments"], [S.ZERO] * S.MAX_ORDER)
        self.assertEqual(full["coefficients"], S.discrete_ode_coefficients(S.MAX_ORDER)["coefficients"])
        for order in range(S.MAX_ORDER + 1):
            with self.subTest(order=order):
                short = S.gaussian_coefficients(order)
                self.assertEqual(short["coefficients"], full["coefficients"][:order + 1])
                self.assertEqual(short["coefficients"], S.discrete_ode_coefficients(order)["coefficients"])

    def test_independent_discrete_equations(self):
        equations = S.discrete_ode_coefficients(4)["equations"]
        self.assertEqual([equation["z_power"] for equation in equations], [4, 5, 6, 7])
        expected_constants = [S.Q2(F(17, 6)), S.Q2(0, F(-6409, 576)),
                              S.Q2(F(18114133, 276480)), S.Q2(0, F(-13052721749, 79626240))]
        for j, equation in enumerate(equations, 1):
            self.assertEqual(equation["slope"], (8 * j * S.SQRT2).data())
            self.assertEqual(equation["constant"], expected_constants[j - 1].data())

    def test_log_coefficients(self):
        c = S.gaussian_coefficients(2)["coefficients"]
        self.assertEqual(c[2] - c[1]**2 / 2, S.Q2(F(85, 128)))
        self.assertEqual(c[2] - c[1]**2 / 2 + F(1, 6), S.Q2(F(319, 384)))

    def test_public_order_validation(self):
        for route in (S.local_amplitude, S.gaussian_coefficients,
                      S.discrete_ode_coefficients, S.verify_symbolic):
            for value in (True, False, 1.0, "1", None, F(1)):
                with self.subTest(route=route.__name__, value=value):
                    with self.assertRaises(TypeError):
                        route(value)
            for value in (-1, S.MAX_ORDER + 1, 10**100):
                with self.subTest(route=route.__name__, value=value):
                    with self.assertRaises(ValueError):
                        route(value)
        for value in (True, -1, 6 * S.MAX_ORDER + 7):
            with self.assertRaises((TypeError, ValueError)):
                S.gaussian_moment(value)

    def test_integrated_receipt(self):
        report = S.verify_symbolic(4)
        self.assertEqual(report["status"], "PASS")
        self.assertEqual(len(report["coefficients"]), 5)
        self.assertEqual(report["odd_epsilon_coefficients"], ["0"] * 4)


if __name__ == "__main__":
    print(f"Report168 symbolic tests; Python {sys.version.split()[0]}; optimize={sys.flags.optimize}", flush=True)
    unittest.main(verbosity=2)
