#!/usr/bin/env python3
import unittest

from zariski_descent import (
    IntegerRing,
    LocalFraction,
    ModRing,
    cech_delta_p1,
    cech_normal_form_p1,
    check_contracting_homotopy,
    glue_principal_cover,
    p1_h0_pair,
    power_cover_coefficients,
    projective_space_cohomology_ranks,
    verify_ideal_certificate,
    verify_power_cover,
)


class ZariskiDescentTests(unittest.TestCase):
    def test_power_cover_integer(self) -> None:
        ring = IntegerRing()
        for n in range(1, 8):
            d = power_cover_coefficients(ring, [2, 3], [-1, 1], n)
            self.assertTrue(verify_power_cover(ring, [2, 3], d, n))

    def test_power_cover_zero_divisors(self) -> None:
        ring = ModRing(12)
        for n in range(1, 7):
            d = power_cover_coefficients(ring, [3, 4], [3, 1], n)
            self.assertTrue(verify_power_cover(ring, [3, 4], d, n))

    def test_glue_integer(self) -> None:
        result = glue_principal_cover(
            IntegerRing(),
            [2, 3],
            [-1, 1],
            [LocalFraction(34, 1), LocalFraction(153, 2)],
            [[0, 0], [0, 0]],
        )
        self.assertEqual(result.global_section, 17)

    def test_glue_zero_divisors(self) -> None:
        ring = ModRing(12)
        result = glue_principal_cover(
            ring,
            [3, 4],
            [3, 1],
            [LocalFraction(9, 0), LocalFraction(8, 0)],
            [[0, 1], [1, 0]],
        )
        self.assertTrue(ring.eq(result.global_section, 5))

    def test_ideal_certificate(self) -> None:
        self.assertTrue(
            verify_ideal_certificate(
                {4: 1}, {0: 4}, [{2: 1, 0: -2}], [{2: 1, 0: 2}]
            )
        )

    def test_p1_normal_form(self) -> None:
        c = {-5: 7, -2: 11, -1: 13, 0: 17, 3: 19}
        nf = cech_normal_form_p1(-3, c)
        self.assertEqual(nf.obstruction, {-2: 11, -1: 13})
        reconstructed = cech_delta_p1(-3, nf.chart_zero, nf.chart_one)
        for e, a in nf.obstruction.items():
            reconstructed[e] = reconstructed.get(e, 0) + a
        self.assertEqual(reconstructed, c)

    def test_p1_h0(self) -> None:
        a, b = p1_h0_pair(4, [2, 3, 5, 7, 11])
        self.assertEqual(cech_delta_p1(4, a, b), {})
        self.assertEqual(projective_space_cohomology_ranks(1, 4), (5, 0))
        self.assertEqual(projective_space_cohomology_ranks(1, -4), (0, 3))

    def test_mixed_sign_contracting_homotopy(self) -> None:
        for n in range(1, 6):
            full = frozenset(range(n + 1))
            for mask in range(1, 1 << (n + 1)):
                neg = frozenset(i for i in range(n + 1) if mask & (1 << i))
                if neg != full:
                    self.assertTrue(check_contracting_homotopy(n, neg))


if __name__ == "__main__":
    unittest.main(verbosity=2)
