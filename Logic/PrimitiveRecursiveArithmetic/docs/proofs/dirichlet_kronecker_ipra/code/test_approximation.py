"""Exact-rational regression and certificate checks for approximation.py.

These are executed software checks, not Lean or object-iPRA proofs.
Run: python3 test_approximation.py --report verification.json
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import argparse
import json
import random
import unittest

import approximation as ap


COUNTS = {}


def counted(label, amount=1):
    COUNTS[label] = COUNTS.get(label, 0) + amount


class ApproximationTests(unittest.TestCase):
    def test_precision_and_square_root_names(self):
        for denominator in range(1, 258):
            k = ap.precision(denominator)
            self.assertLessEqual(F(1, 1 << k), F(1, denominator))
            counted("precision_bounds")
        for n in (0, 1, 2, 3, 5, 10, 16, 101):
            for k in (0, 1, 2, 3, 8, 17, 40):
                x, eta = ap.sqrt_name(n)(k), F(1, 1 << k)
                self.assertLessEqual(x*x, n)
                self.assertLess(n, (x+eta)*(x+eta))
                counted("sqrt_name_enclosures")

    def test_nearest_integer_negative_and_ties(self):
        for b in range(1, 20):
            for a in range(-40, 41):
                x = F(a, b)
                p = ap.nearest_integer(x)
                self.assertLessEqual(abs(x-p), F(1, 2))
                self.assertEqual(ap.rho(x), abs(x-p))
                self.assertEqual(ap.rho(x), ap.rho(x+7))
                self.assertEqual(ap.rho(x), ap.rho(-x))
                counted("nearest_integer_cases")
        self.assertEqual(ap.nearest_integer(F(-1, 2)), -1)
        self.assertEqual(ap.nearest_integer(F(1, 2)), 0)

    def test_scalar_rational_exhaustive(self):
        for b in range(1, 18):
            for a in range(-18, 19):
                x = F(a, b)
                for N in range(1, 13):
                    result = ap.dirichlet_rational(x, N)
                    q, p = result["q"], result["p"]
                    self.assertTrue(1 <= q <= N)
                    self.assertLessEqual(abs(q*x-p), F(1, N+1))
                    self.assertEqual(abs(q*x-p), result["gap"])
                    counted("sharp_scalar_rational_cases")
        for x in (F(3, 4), F(-1, 4), F(7, 4), F(-5, 4)):
            result = ap.dirichlet_rational(x, 1)
            self.assertEqual(result["wrap"], 1)
            counted("explicit_wrap_cases")

    def test_scalar_name_transfer(self):
        for x in (F(0), F(1, 2), F(-7, 3), F(19, 29), F(-1001, 97)):
            for N in (1, 2, 3, 5, 13, 32):
                result = ap.dirichlet_scalar(ap.rational_name(x), N)
                actual = abs(result["q"]*x-result["p"])
                self.assertLessEqual(actual, result["linear_error_bound"])
                self.assertLess(result["linear_error_bound"], F(1, N))
                counted("scalar_name_transfer_cases")

    def test_simultaneous_arbitrary_N(self):
        rng = random.Random(20261114)
        Ns = (1, 2, 3, 4, 5, 8, 12, 17, 24)
        for d in range(1, 5):
            for N in Ns:
                for variant in range(4):
                    if variant == 0:
                        xs = [F(j+1, 2) for j in range(d)]
                    elif variant == 1:
                        xs = [F((-1)**j*(N+j), N+1) for j in range(d)]
                    else:
                        xs = [F(rng.randint(-100, 100), rng.randint(1, 53))
                              for _ in range(d)]
                    result = ap.dirichlet_simultaneous(
                        [ap.rational_name(x) for x in xs], N)
                    q, ps = result["q"], result["p"]
                    self.assertTrue(1 <= q <= N)
                    self.assertLess(result["R"], result["S"])
                    self.assertLess(N*result["S"]**d, 1)
                    self.assertGreater(result["grid_count"], result["residue_colors"])
                    for x, p, upper in zip(xs, ps, result["linear_error_bounds"]):
                        self.assertLessEqual(abs(q*x-p), upper)
                        self.assertLess(upper, result["S"])
                        self.assertLess(N*upper**d, 1)
                    counted("simultaneous_rational_vectors")
        for d in range(1, 5):
            names = [ap.sqrt_name(n) for n in (2, 3, 5, 7)[:d]]
            for N in (1, 2, 5, 11, 23):
                result = ap.dirichlet_simultaneous(names, N)
                k = result["precision"]+8
                eta = F(1, 1 << k)
                for name, p in zip(names, result["p"]):
                    lo = result["q"]*name(k)-p
                    hi = lo+result["q"]*eta
                    enclosure = max(abs(lo), abs(hi))
                    self.assertLess(N*enclosure**d, 1)
                counted("simultaneous_sqrt_vectors")

    def test_padded_unbounded_denominators(self):
        for x in (F(0), F(1, 2), F(-2, 7), F(7, 3)):
            for B in (0, 1, 2, 5, 9, 17):
                result = ap.unbounded_denominator(ap.rational_name(x), B)
                q, p = result["q"], result["p"]
                self.assertTrue(B < q <= (B+1)**3)
                self.assertLess(q*abs(q*x-p), 1)
                self.assertLess(q*result["linear_error_bound"], 1)
                counted("padded_denominator_cases")
        result = ap.unbounded_denominator(ap.rational_name(F(1, 2)), 17)
        self.assertGreater(result["q"], 17)
        self.assertEqual(F(result["p"], result["q"]), F(1, 2))
        self.assertEqual(result["q"]//gcd(result["q"], result["p"]), 2)
        counted("padding_distinguished_from_reduced_denominators")

    def test_rational_compatibility_and_search(self):
        cases = [
            ([[F(1, 2)]], [F(1, 2)], True),
            ([[F(1, 2)]], [F(1, 3)], False),
            ([[F(2, 3), F(1, 3)]], [F(1, 3), F(2, 3)], True),
            ([[F(2, 3), F(1, 3)]], [F(1, 3), F(1, 3)], False),
            ([[F(1, 2), F(0)], [F(0), F(1, 3)]], [F(1, 2), F(2, 3)], True),
            ([[F(1, 2), F(0)], [F(0), F(1, 3)]], [F(1, 4), F(2, 3)], False),
            ([[F(-1, 5)]], [F(17, 5)], True),
            ([[F(0)]], [F(1, 2)], False),
        ]
        for matrix, beta, expected in cases:
            result = ap.rational_compatibility(matrix, beta)
            self.assertEqual(result["compatible"], expected)
            counted("rational_compatibility_cases")
            if not expected:
                h = result["h"]
                self.assertTrue(all(ap.rho(sum(x*y for x, y in zip(h, row))) == 0
                                    for row in matrix))
                self.assertNotEqual(ap.rho(sum(x*y for x, y in zip(h, beta))), 0)
                counted("verified_exact_obstructions")
                continue
            for H in (1, 2, 5):
                delta = F(1, 128*len(beta)*H*(result["C"]+1))
                cert = ap.interval_compatibility(matrix, beta, H, result["C"], delta)
                self.assertTrue(cert["valid"])
                counted("rational_interval_certificates")
            for s in (2, 5, 11):
                found = ap.kronecker_search(
                    [[ap.rational_name(x) for x in row] for row in matrix],
                    [ap.rational_name(x) for x in beta], s, result["C"])
                for j in range(len(beta)):
                    residual = sum(found["q"][i]*matrix[i][j] for i in range(len(matrix)))
                    residual -= beta[j]+found["p"][j]
                    self.assertLess(abs(residual), F(1, s))
                    self.assertLessEqual(abs(residual), found["linear_error_bounds"][j])
                counted("rational_kronecker_witnesses")
        bad = ap.interval_compatibility([[F(1, 2)]], [F(1, 3)], 2, 6, F(0))
        self.assertFalse(bad["valid"])
        self.assertGreater(bad["U"], F(1, 8)+6*bad["L"])
        counted("interval_certificate_rejections")

    def test_sqrt2_separation_and_positive_kronecker(self):
        name = ap.sqrt_name(2)
        x, eta = name(40), F(1, 1 << 40)
        for H in (1, 2, 5, 16, 64, 257):
            for h in range(1, H+1):
                self.assertGreater(ap.rho(h*x)-h*eta, F(1, 4*H))
                counted("sqrt2_separation_values")
            C = 4*H
            k = ap.precision(64*H*(C+1))
            delta = F(1, 1 << k)
            cert = ap.interval_compatibility([[name(k)]], [F(1, 3)], H, C, delta)
            self.assertTrue(cert["valid"])
            counted("sqrt2_interval_certificates")
        for beta in (F(1, 3), F(-7, 4), F(12, 7)):
            for s in (2, 3, 5, 9, 16):
                for B in (0, 1, 7, 25):
                    result = ap.kronecker_positive(name, ap.rational_name(beta), s,
                                                   lambda H: 4*H, B)
                    q, p = result["q"], result["p"]
                    self.assertTrue(B < q <= result["upper_q_bound"])
                    k = result["precision"]+8
                    lo = q*name(k)-p-beta
                    hi = lo+F(q, 1 << k)
                    self.assertLess(max(abs(lo), abs(hi)), F(1, s))
                    self.assertLess(result["linear_error_bound"], F(7, 8*s))
                    counted("positive_sqrt2_kronecker_witnesses")

    def test_bounded_enumeration(self):
        for N in (1, 2, 3, 4):
            for dimension in (1, 2, 3):
                points = list(ap.expanding_box(N, dimension))
                self.assertEqual(len(points), (2*N-1)**dimension)
                self.assertEqual(len(points), len(set(points)))
                self.assertTrue(all(max(map(abs, q)) < N for q in points))
                counted("bounded_box_enumerations")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    options = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ApproximationTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if options.report:
        options.report.write_text(json.dumps({
            "status": "passed" if result.wasSuccessful() else "failed",
            "tests_run": result.testsRun,
            "failures": len(result.failures),
            "errors": len(result.errors),
            "checks": COUNTS,
            "arithmetic": "Python fractions.Fraction and exact integers; no floating point",
            "scope": "Executed reference-implementation checks, not a formal proof",
        }, indent=2)+"\n")
    raise SystemExit(0 if result.wasSuccessful() else 1)
