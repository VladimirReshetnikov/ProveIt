#!/usr/bin/env python3
"""Exact finite checks. These do not certify a representative-cover hypothesis."""

import json
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "code"))
from elliptic import (EllipticCurve, ceil_log2, determinant, homogeneous_eval,
                      integer_height, point_text, rational_roots,
                      rational_square_roots, verify_polynomial_certificate, x_height)


def independent_affine_scan(curve, bound):
    """A second enumeration: scan all reduced rational x=p/q, q<=bound."""
    out = {None} if bound else set()
    for q in range(1, bound + 1):
        for p in range(-bound, bound + 1):
            if gcd(p, q) != 1:
                continue
            x = Fraction(p, q)
            r = x ** 3 + curve.A * x + curve.B
            if r < 0:
                continue
            u, v = isqrt(r.numerator), isqrt(r.denominator)
            if u * u != r.numerator or v * v != r.denominator:
                continue
            y = Fraction(u, v)
            out.add((x, y))
            out.add((x, -y))
    return out


class EllipticChecks(unittest.TestCase):
    def test_binary_heights(self):
        for n in range(1, 1000):
            h = ceil_log2(n)
            self.assertLessEqual(n, 1 << h)
            if h:
                self.assertGreater(n, 1 << (h - 1))
        self.assertEqual(integer_height(None), 0)

    def test_reject_singular_and_invalid(self):
        with self.assertRaises(ValueError):
            EllipticCurve(0, 0)
        with self.assertRaises(ValueError):
            EllipticCurve(-1, 0).point(2, 2)
        with self.assertRaises(ValueError):
            EllipticCurve(-1, 0).descent_data([])

    def test_determinant(self):
        self.assertEqual(determinant([]), 1)
        self.assertEqual(determinant([[0, 2], [3, 4]]), -6)
        self.assertEqual(determinant([[1, 2, 3], [2, 4, 6], [7, 8, 9]]), 0)

    def test_rational_roots(self):
        self.assertEqual(rational_roots([0, 6, -5, 1]),
                         [Fraction(0), Fraction(2), Fraction(3)])
        self.assertEqual(rational_roots([-1, 1, 2]),
                         [Fraction(-1), Fraction(1, 2)])
        self.assertEqual(rational_roots([0, 0, 3]), [Fraction(0)])
        self.assertEqual(rational_roots([5]), [])
        self.assertEqual(rational_roots([1, 0, 1]), [])
        self.assertEqual(rational_square_roots(Fraction(4, 9)),
                         [Fraction(-2, 3), Fraction(2, 3)])
        self.assertEqual(rational_square_roots(Fraction(2, 3)), [])
        with self.assertRaises(ValueError):
            rational_roots([0, 0])

    def test_exact_division(self):
        curve = EllipticCurve(-1, 1)
        base = curve.point(0, 1)
        for n in range(-3, 4):
            p = curve.mul(n, base)
            target = curve.mul(2, p)
            answers = curve.halves(target)
            self.assertIn(p, answers)
            self.assertEqual(len(answers), len(set(answers)))
            self.assertTrue(all(curve.mul(2, q) == target for q in answers))
        e1 = EllipticCurve(-1, 0)
        points = e1.enumerate_points(1)
        self.assertEqual(set(e1.halves(None)), set(points))
        for p in points[1:]:
            self.assertEqual(e1.halves(p), [])
        for p in points:
            i, q = e1.division_by_representatives(p, points)
            self.assertEqual(e1.add(e1.mul(2, q), points[i]), p)
        self.assertIsNone(e1.division_by_representatives(e1.point(1, 0), [None]))

    def test_polynomial_certificates(self):
        for a, b in [(-1, 0), (-1, 1), (-2, 1), (0, 1), (2, 3)]:
            curve = EllipticCurve(a, b)
            cert = curve.duplication_certificate()
            self.assertTrue(verify_polynomial_certificate(cert))
            raw = curve.duplication_certificate(normalize=False)
            self.assertTrue(verify_polynomial_certificate(raw))
            factor = cert["normalization_factor"]
            self.assertGreater(factor, 0)
            self.assertEqual(raw["R"], cert["sylvester_determinant"])
            self.assertEqual(raw["R"], factor * cert["R"])
            self.assertEqual(raw["L"], factor * cert["L"])
            for field in ("A_X", "B_X", "A_Z", "B_Z"):
                self.assertEqual(raw[field], [factor * c for c in cert[field]])
            bad = dict(cert)
            bad["R"] += 1
            self.assertFalse(verify_polynomial_certificate(bad))
            changed_label = dict(cert)
            changed_label["A"] = "unverified metadata"
            self.assertTrue(verify_polynomial_certificate(changed_label))
            for x in range(-12, 13):
                for z in range(0, 13):
                    if gcd(x, z) != 1:
                        continue
                    fx = homogeneous_eval(cert["F"], x, z)
                    gx = homogeneous_eval(cert["G"], x, z)
                    divisor = gcd(fx, gx)
                    self.assertGreater(divisor, 0)
                    self.assertEqual(cert["R"] % divisor, 0)
                    image_height = max(abs(fx), abs(gx)) // divisor
                    self.assertLessEqual(max(abs(x), z) ** 4,
                                         cert["L"] * image_height)

    def test_enumeration_against_independent_scan(self):
        for a, b in [(-1, 0), (-1, 1), (-2, 1), (0, 1), (2, 3)]:
            curve = EllipticCurve(a, b)
            for bound in (0, 1, 2, 4, 9, 16):
                points = curve.enumerate_points(bound)
                self.assertEqual(len(points), len(set(points)))
                self.assertEqual(set(points), independent_affine_scan(curve, bound))
                self.assertTrue(all(curve.contains(p) and x_height(p) <= bound
                                    for p in points))

    def test_e1_list_and_group_table(self):
        curve = EllipticCurve(-1, 0)
        points = [None, curve.point(-1, 0), curve.point(0, 0), curve.point(1, 0)]
        self.assertEqual(set(curve.enumerate_points(256)), set(points))
        cert = curve.duplication_certificate()
        self.assertEqual(cert["sylvester_determinant"], 4096)
        self.assertEqual(cert["normalization_factor"], 256)
        self.assertEqual((cert["R"], cert["L"]), (16, 36))
        self.assertEqual(curve.descent_data(points)["C"], 12)
        for i, p in enumerate(points):
            for j, q in enumerate(points):
                self.assertEqual(curve.add(p, q), points[i ^ j])

    def test_group_formulas_and_height_bounds(self):
        curve = EllipticCurve(-1, 1)
        base = curve.point(0, 1)
        points = [curve.mul(n, base) for n in range(-10, 11)]
        representatives = [curve.mul(n, base) for n in range(-3, 4)]
        cert = curve.duplication_certificate()
        data = curve.descent_data(representatives)
        self.assertFalse(data["coverage_verified"])
        for n, p in zip(range(-10, 11), points):
            self.assertTrue(curve.contains(p))
            self.assertEqual(curve.add(p, curve.neg(p)), None)
            self.assertLessEqual(x_height(p) ** 4,
                                 cert["L"] * x_height(curve.mul(2, p)))
            for r, t in zip(representatives, data["T"]):
                self.assertLessEqual(x_height(curve.sub(p, r)), t * x_height(p) ** 2)
                target = curve.add(curve.mul(2, p), r)
                self.assertLessEqual(integer_height(p), integer_height(target) + data["C"])
            for m in range(-3, 4):
                self.assertEqual(curve.add(p, curve.mul(m, base)),
                                 curve.mul(n + m, base))


def write_metadata(result):
    e1 = EllipticCurve(-1, 0)
    sample = EllipticCurve(-1, 1)
    points = [None, e1.point(-1, 0), e1.point(0, 0), e1.point(1, 0)]
    table = [[points.index(e1.add(p, q)) for q in points] for p in points]
    base = sample.point(0, 1)
    reps = [sample.mul(n, base) for n in range(-3, 4)]
    report = {
        "purpose": "Exact finite arithmetic and certificate checks, not a proof of quotient coverage",
        "tests_run": result.testsRun,
        "failures": len(result.failures), "errors": len(result.errors),
        "successful": result.wasSuccessful(),
        "polynomial_certificates": [EllipticCurve(a, b).duplication_certificate()
                                    for a, b in [(-1, 0), (-1, 1), (-2, 1), (0, 1), (2, 3)]],
        "enumeration_cross_checks": {"curves": [[-1, 0], [-1, 1], [-2, 1], [0, 1], [2, 3]],
                                     "bounds": [0, 1, 2, 4, 9, 16],
                                     "algorithms": ["square/cube denominators", "all reduced rational x"]},
        "E1": {"search_bound": 256,
               "points": [point_text(p) for p in e1.enumerate_points(256)],
               "table_order": [point_text(p) for p in points],
               "addition_table_indices": table,
               "descent_constants_with_all_four_representatives": e1.descent_data(points)},
        "sample_curve": {"A": -1, "B": 1, "base_point": point_text(base),
                         "tested_multiples": [-10, 10],
                         "representative_multiples": [-3, 3],
                         "computed_constants": sample.descent_data(reps)},
        "exact_division": {
            "algorithm": "rational-root theorem for the duplication quartic, rational square roots, exact double check",
            "round_trip_curve": [-1, 1], "round_trip_multiples": [-3, 3],
            "E1_halves_of_O": [point_text(q) for q in e1.halves(None)],
            "E1_halves_of_nonidentity_points":
                {point_text(p): [point_text(q) for q in e1.halves(p)] for p in points[1:]},
            "sample_round_trip": [
                {"n": n, "point": point_text(sample.mul(n, base)),
                 "double": point_text(sample.mul(2 * n, base)),
                 "halves": [point_text(q) for q in sample.halves(sample.mul(2 * n, base))]}
                for n in range(4)]
        },
        "logical_limits": [
            "The bound-256 enumeration does not alone prove the complete E1 list; the report's Fermat descent does.",
            "Sampled height inequalities are finite implementation checks; general inequalities are proved in the report.",
            "No representative-cover hypothesis is certified by these tests.",
            "The exhaustive bounded_division_search was not executed at its very large automatic bound.",
            "The Python implementation is not an embedded Prf PRAAx proof object."
        ],
    }
    destination = ROOT / "metadata" / "elliptic_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return destination


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(EllipticChecks)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    print("Metadata:", write_metadata(result))
    raise SystemExit(0 if result.wasSuccessful() else 1)
