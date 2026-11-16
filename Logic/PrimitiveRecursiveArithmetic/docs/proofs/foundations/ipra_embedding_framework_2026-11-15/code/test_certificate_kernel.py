#!/usr/bin/env python3
from fractions import Fraction
from pathlib import Path
import json
import unittest

from certificate_kernel import (
    CertificateError,
    TraceCertificate,
    exact_branch_with_gap,
    finite_grid_minimum,
    finite_regularity_check,
    height_bound_to_list,
    list_to_height_bound,
    overlapping_branch,
    polynomial_eval,
    polynomial_lipschitz,
    sqrt2_midpoint,
    verify_framework_certificate,
    verify_trace,
)


class KernelTests(unittest.TestCase):
    def test_polynomial(self) -> None:
        self.assertEqual(polynomial_eval([-2, 0, 1], Fraction(3, 2)), Fraction(1, 4))
        self.assertEqual(polynomial_lipschitz([-2, 0, 1], 2), 4)

    def test_trace(self) -> None:
        u, b = 3, 8
        states = tuple(i * u + i * (i - 1) // 2 for i in range(b + 1))
        cert = TraceCertificate(u, b, 0, states, states[-1])
        verify_trace(
            cert,
            step=lambda u, i, s: s + u + i,
            invariant=lambda u, i, s: s == i * u + i * (i - 1) // 2,
            accept=lambda _u, s: s,
        )

    def test_trace_rejects(self) -> None:
        cert = TraceCertificate(1, 1, 0, (0, 9), 9)
        with self.assertRaises(CertificateError):
            verify_trace(cert, lambda u, i, s: s + u + i, lambda u, i, s: True, lambda u, s: s)

    def test_overlapping_branch(self) -> None:
        d = overlapping_branch(Fraction(9, 16), Fraction(1, 32), Fraction(1, 2), Fraction(1, 8))
        self.assertEqual(d.branch, "upper")
        d = overlapping_branch(Fraction(3, 4), Fraction(1, 32), Fraction(1, 2), Fraction(1, 8))
        self.assertEqual(d.branch, "lower")

    def test_exact_branch(self) -> None:
        self.assertEqual(exact_branch_with_gap(Fraction(7, 8), Fraction(1, 32), Fraction(1, 2), Fraction(1, 4)), "above")

    def test_grid(self) -> None:
        w = finite_grid_minimum([-2, 0, 1], Fraction(1), Fraction(2), 16)
        self.assertEqual(w.point, Fraction(23, 16))
        self.assertEqual(w.residual, Fraction(17, 256))

    def test_sqrt2_regularity(self) -> None:
        finite_regularity_check(sqrt2_midpoint, 12)

    def test_height_equivalence(self) -> None:
        pred = lambda a, x: x * x <= a
        points = height_bound_to_list(20, 4, pred)
        self.assertEqual(points, [0, 1, 2, 3, 4])
        self.assertEqual(list_to_height_bound(points), 4)

    def test_example_certificate(self) -> None:
        path = Path(__file__).resolve().parents[1] / "examples" / "framework_certificate.json"
        data = json.loads(path.read_text(encoding="utf-8"))
        report = verify_framework_certificate(data)
        self.assertEqual(report["robust_branch"], "upper")
        self.assertEqual(report["net_point"], "23/16")


if __name__ == "__main__":
    unittest.main(verbosity=2)
