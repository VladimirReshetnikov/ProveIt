#!/usr/bin/env python3
from fractions import Fraction
import unittest

from scr_reference import (
    all_permutations,
    bounded_curve_points,
    cubic_bisection_certificate,
    digit,
    least_accepted,
    least_path_certificate,
    pack_digits,
    stable_observation,
    symmetric_root_observation,
    unpack_digits,
    verify_bounded_curve_list,
    verify_cubic_bisection_certificate,
    verify_state_path,
)


class SCRReferenceTests(unittest.TestCase):
    def test_mixed_digits_roundtrip(self) -> None:
        digits = [4, 0, 3, 1, 2]
        code = pack_digits(digits, 5)
        self.assertEqual(unpack_digits(code, len(digits), 5), digits)
        self.assertEqual(digit(code, 10, 5), 0)

    def test_least_accepted(self) -> None:
        self.assertEqual(least_accepted(20, lambda n: n * n >= 50), 8)
        self.assertEqual(least_accepted(7, lambda _: False), 7)

    def test_whole_path_beats_greedy_dead_end(self) -> None:
        edges = {(0, 1), (0, 2), (1, 1), (2, 3), (3, 4)}
        cert = least_path_certificate(
            base=5,
            horizon=3,
            start=0,
            edge=lambda a, b: (a, b) in edges,
            goal=lambda s: s == 4,
        )
        self.assertIsNotNone(cert)
        assert cert is not None
        self.assertEqual(cert.states, (0, 2, 3, 4))
        ok, _ = verify_state_path(
            cert.code,
            base=cert.base,
            horizon=cert.horizon,
            start=0,
            edge=lambda a, b: (a, b) in edges,
            goal=lambda s: s == 4,
        )
        self.assertTrue(ok)

    def test_cubic_bisection_exact(self) -> None:
        cert = cubic_bisection_certificate(Fraction(2), Fraction(0), Fraction(2), 12)
        self.assertTrue(verify_cubic_bisection_certificate(cert))
        self.assertEqual(cert.final_hi - cert.final_lo, Fraction(2, 2**12))

    def test_cubic_tamper_rejected(self) -> None:
        cert = cubic_bisection_certificate(Fraction(2), Fraction(0), Fraction(2), 8)
        from dataclasses import replace

        bad = replace(cert, branch_code=cert.branch_code ^ 1)
        self.assertFalse(verify_cubic_bisection_certificate(bad))

    def test_stable_observer_erases_root_order(self) -> None:
        roots = (Fraction(-2), Fraction(1), Fraction(3))
        certs = all_permutations(roots)
        obs = stable_observation(
            certs,
            valid=lambda c: sorted(c) == sorted(roots),
            observe=symmetric_root_observation,
        )
        self.assertEqual(obs, (Fraction(2), Fraction(-6), Fraction(14)))

    def test_unstable_observer_detected(self) -> None:
        roots = (Fraction(-2), Fraction(1), Fraction(3))
        certs = all_permutations(roots)
        with self.assertRaises(ValueError):
            stable_observation(certs, valid=lambda _: True, observe=lambda c: c[0])

    def test_height_list(self) -> None:
        points = bounded_curve_points(12)
        self.assertTrue(verify_bounded_curve_list(12, points))
        self.assertFalse(verify_bounded_curve_list(12, points[:-1]))


if __name__ == "__main__":
    unittest.main(verbosity=2)
