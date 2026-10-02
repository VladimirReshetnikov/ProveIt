"""Finite checks and regression tests; none certify an asymptotic theorem."""

from math import comb
from pathlib import Path
import json
import unittest

import mpmath as mp
import numpy as np
import sympy as S

from check_shift import cosine_coefficients, evaluate, logdet, moments, selberg, sf
from density import density, endpoint, right_endpoint_log_weight
from verify_symbolic import verify
from verify_c1_log_shift import verify as verify_log_shift
from check_first_correction_trace import verify as verify_trace
from evaluate_c1 import coefficient


class ReplayTests(unittest.TestCase):
    def test_exact_moments(self):
        actual = moments(30)
        expected = [sum(comb(n, j)**2 * comb(n+j, j)**2 for j in range(n+1))
                    for n in range(31)]
        self.assertEqual(actual, expected)
        self.assertEqual(moments(0), [1])

    def test_dct_normalization(self):
        theta = np.pi * (np.arange(64) + 0.5) / 64
        coeff = cosine_coefficients(np.cos(theta))
        self.assertAlmostEqual(coeff[1], 0.5, places=14)
        Q = sum(k * coeff[k]**2 for k in range(1, 64)) / 2
        self.assertAlmostEqual(Q, 1/8, places=14)

    def test_apery_logdet_against_direct_small_determinants(self):
        with mp.workdps(90):
            for N, r in ((1, 0), (2, 1), (4, 3), (6, 2)):
                A = moments(r + 2*N - 2)
                raw = mp.det(mp.matrix([[A[r+i+j] for j in range(N)]
                                       for i in range(N)]))
                expected = mp.log(raw) - N*(r+N-1)*mp.log(endpoint())
                self.assertLess(abs(logdet(N, r, 90) - expected), mp.mpf("1e-65"))

    def test_selberg_against_beta_moment_determinants(self):
        with mp.workdps(90):
            for N, r in ((1, 0), (2, 1), (5, 3)):
                matrix = mp.matrix([[mp.beta(r+i+j+1, mp.mpf("1.5"))
                                     for j in range(N)] for i in range(N)])
                self.assertLess(abs(mp.log(mp.det(matrix)) - selberg(N, r)),
                                mp.mpf("1e-65"))

    def test_density_endpoint_and_continuation(self):
        with mp.workdps(60):
            C = endpoint()
            # The first point requires the added continuation term.
            for x in (mp.mpf("0.08"), mp.mpf("0.3"), mp.mpf("3")):
                self.assertGreater(density(x), 0)
            crossing = 2 / (7 + 3*mp.sqrt(5))
            left = density(crossing*(1-mp.mpf("1e-12")))
            right = density(crossing*(1+mp.mpf("1e-12")))
            self.assertLess(abs(left/right - 1), mp.mpf("1e-9"))
            epsilon = mp.mpf("1e-16")
            endpoint_value = mp.log(C*density(C*(1-epsilon))/mp.sqrt(epsilon))
            self.assertLess(abs(endpoint_value - right_endpoint_log_weight()),
                            mp.mpf("1e-14"))

    def test_domain_checks(self):
        with self.assertRaises(ValueError):
            density(0)
        with self.assertRaises(ValueError):
            sf("0.05", M=8)
        with self.assertRaises(ValueError):
            evaluate("0.1", M=8, sizes=(11,))

    def test_reference_constants(self):
        expected_dir = Path(__file__).resolve().parents[1] / "expected"
        for suffix, s, M in (("s01", "0.1", 128), ("s02", "0.2", 128), ("s1", "1", 64)):
            expected = json.loads((expected_dir / f"numerics_{suffix}.json").read_text())
            actual = sf(s, M=M)
            # These smaller grids are a fast regression, not the full replay.
            for name in ("F", "f0", "bias", "Q", "E"):
                self.assertAlmostEqual(actual[name], expected["constants"][name], places=9)

    def test_symbolic(self):
        self.assertTrue(verify()["status"].startswith("PASS"))

    def test_first_correction_log_shift(self):
        self.assertTrue(verify_log_shift()["status"].startswith("PASS"))

    def test_first_correction_trace_cumulants(self):
        self.assertTrue(verify_trace()["status"].startswith("PASS"))

    def test_first_correction_endpoint_identity(self):
        # Exact algebra after the proved energy identity is substituted.
        a, s, Up, Upp = S.symbols("a s U_prime U_second", positive=True)
        D = 2*a**S.Rational(3, 2)*(1-a)*Up/s
        Sp = -(1-a)*Up**2/2
        original = (D*Sp/6 + D*Up/8 + D/24*(1/(1-a)+S.Rational(3, 2)/a)
                    + a**S.Rational(3, 2)*((1-a)*Upp-Up)/(12*s))
        simplified = (S.sqrt(a)*(1-a)/(24*s)
                      * (-4*a*(1-a)*Up**3 + 6*a*Up**2 + 3*Up + 2*a*Upp))
        self.assertEqual(S.simplify(original-simplified), 0)
        # Independent DCT derivative sum versus the endpoint identity.
        result = coefficient("1", M=64)
        self.assertLess(abs(float(result["S_prime_identity_residual"])), 1e-12)
        self.assertLess(abs(float(result["c_rel_formula_difference"])), 1e-14)


if __name__ == "__main__":
    unittest.main()
