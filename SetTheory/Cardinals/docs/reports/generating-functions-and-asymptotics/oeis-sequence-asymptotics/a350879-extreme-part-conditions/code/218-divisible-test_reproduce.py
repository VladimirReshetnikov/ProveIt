#!/usr/bin/env python3
"""Boundary/regression tests; standard library, no saved-output dependencies."""
from fractions import Fraction as F
import unittest

import reproduce as r
import uniform_certificates as u


class ExactTests(unittest.TestCase):
    def test_count_boundaries(self):
        self.assertEqual(r.partition_numbers(0), [1])
        self.assertEqual(r.divisible_counts(0), [0])
        self.assertEqual(r.conjugate_counts(0), ([0], [1]))
        self.assertEqual(list(r.enumerate_partitions(0)), [()])
        self.assertEqual(r.partition_numbers(6), [1, 1, 2, 3, 5, 7, 11])
        self.assertEqual(r.divisible_counts(10), [0, 1, 2, 3, 5, 6, 11, 12, 20, 26, 37])
        for N in (1, 2, 5, 12, 50):
            a, p = r.conjugate_counts(N)
            self.assertEqual(a, r.divisible_counts(N))
            self.assertEqual(p, r.partition_numbers(N))
            self.assertEqual(p, r.partition_numbers_knapsack(N))

    def test_radial_and_derivative(self):
        expected = [F(0), F(1, 2), F(1, 12), F(1, 12), F(89, 720),
                    F(61, 240), F(20287, 30240), F(21841, 10080), F(10023809, 1209600)]
        self.assertEqual(r.radial_coefficients(8), expected)
        self.assertEqual(r.radial_moments(8), expected)
        self.assertEqual(r.radial_coefficients(0), [F(0)])
        self.assertEqual(r.radial_moments(0), [F(0)])
        self.assertEqual(r.derivative_polynomials(0), [[F(1), F(-1, 2)]])
        self.assertEqual(r.correction_coefficients(0), [{0: F(1)}])
        self.assertEqual(r.correction_coefficients(2)[2],
                         {0: F(1, 6), 1: F(-1, 2), 2: F(3, 4)})

    def test_fourier_edges(self):
        for N in (0, 1, 4, 12):
            for k in (1, 2, 5):
                for m in (2, 3):
                    self.assertEqual(r.fixed_minimum_residues(N, k, m),
                                     r.fourier_reduction(N, k, m))

    def test_inverse(self):
        self.assertEqual(r.inverse_coefficients(2, [1, -1, 0, 0], 3),
                         [F(1), F(5, 2), F(13, 3)])
        self.assertEqual(r.inverse_coefficients(3, [1, 0, 0, 0], 3), [0, 0, 0])
        self.assertEqual(r.inverse_coefficients(2, [1, F(2, 3)], 1), [F(-2, 3)])

    def test_certificate_edges(self):
        self.assertEqual(r.exp_negative_upper(0), 1)
        p = r.partition_numbers(40)
        a = r.divisible_counts(40)
        for K in (2, 3, 4):
            z = r.finite_enclosure(40, K, F(4, 5), p)
            self.assertLessEqual(int(z['lower_integer']), p[40] - a[40])
            self.assertGreaterEqual(int(z['upper_integer']), p[40] - a[40])

    def test_input_domains(self):
        self.assertEqual(r._validation_checks(), 22)
        functions = [r.partition_numbers, r.partition_numbers_knapsack, r.divisible_counts,
                     r.conjugate_counts, r.radial_coefficients, r.radial_moments,
                     r.derivative_polynomials, r.correction_coefficients]
        for function in functions:
            for x in (True, False, 1.0, F(1), '1', None):
                with self.subTest(function=function.__name__, value=x):
                    with self.assertRaises(TypeError):
                        function(x)
            with self.assertRaises(ValueError):
                function(-1)
        for x in (True, False, 1.0, '1', None):
            with self.assertRaises(TypeError):
                list(r.enumerate_partitions(x))
        with self.assertRaises(TypeError):
            r.finite_enclosure(20, 2, F(1, 2), [True] * 21)
        with self.assertRaises(ValueError):
            r.finite_enclosure(20, 2, F(1, 2), [1])

    def test_uniform_certificates(self):
        receipt = u.endpoint_certificates()
        self.assertEqual(receipt['endpoint_count'], 19)
        self.assertEqual(receipt['onset_n'], 90)
        self.assertEqual(receipt['onset_upper'], '6935272345/77070336')
        self.assertEqual(receipt['w_lower'], '664225/27648')
        self.assertEqual(u.arctan_bounds(F(1, 5), 1), (F(74, 375), F(1, 5)))
        self.assertEqual(u.e_bounds(1), (F(1), F(11, 4)))
        self.assertEqual(u._validation_checks(), 18)
        with self.assertRaises(RuntimeError):
            u._require(False, 'unit-test negative probe')
        for value in (True, False, F(2), '2', None):
            with self.assertRaises(TypeError):
                u.e_bounds(value)
        for value in (True, False, '1/5', None):
            with self.assertRaises(TypeError):
                u.arctan_bounds(value, 2)


if __name__ == '__main__':
    unittest.main()
