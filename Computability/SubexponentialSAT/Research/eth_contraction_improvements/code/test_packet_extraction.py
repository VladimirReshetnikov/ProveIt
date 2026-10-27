#!/usr/bin/env python3
"""Deterministic checks of the local packet coefficient-extraction identity.

These checks do not validate the preprint's global SAT algorithm or its
running-time theorem.  Run: python3 test_packet_extraction.py
"""

from itertools import product
from math import comb, prod
import random
import unittest

from packet_extraction import (
    RingSpec, coefficient_finite_difference, coefficient_reference, v2_factorial,
)


class PacketExtractionTests(unittest.TestCase):
    comparisons = 0

    def compare(self, forms, beta, p, ring=RingSpec()):
        result = coefficient_finite_difference(forms, beta, p, ring)
        self.assertEqual(result.coefficient, coefficient_reference(forms, beta, p, ring))
        if sum(beta) <= len(forms):
            self.assertEqual(result.evaluation_count,
                             prod(b + 1 for b in result.homogenized_exponents))
            self.assertLessEqual(result.evaluation_count, 1 << len(forms))
            self.assertLessEqual(result.working_precision, p + len(forms))
        else:
            self.assertEqual(result.evaluation_count, 0)
        type(self).comparisons += 1

    def test_exhaustive_binary_coefficients(self):
        # All 0/1 affine products through three rows and two mode variables.
        # Repeat at several moduli to exercise integer cancellation.
        for rows in range(4):
            for modes in range(3):
                for values in product(range(2), repeat=rows * (modes + 1)):
                    forms = [tuple((values[i * (modes + 1) + j],)
                                   for j in range(modes + 1)) for i in range(rows)]
                    for beta in product(range(rows + 2), repeat=modes):
                        if sum(beta) > rows + 1:
                            continue
                        for p in (1, 3):
                            self.compare(forms, beta, p)

    def test_exhaustive_mod_four_one_mode(self):
        for rows in range(3):
            for values in product(range(4), repeat=2 * rows):
                forms = [[(values[2 * i],), (values[2 * i + 1],)] for i in range(rows)]
                for degree in range(rows + 2):
                    self.compare(forms, (degree,), 2)

    def test_random_scalar(self):
        rng = random.Random(20261026)
        for _ in range(500):
            rows = rng.randrange(8)
            modes = rng.randrange(5)
            p = rng.randrange(1, 10)
            forms = [[(rng.randrange(-(1 << (p + 2)), 1 << (p + 2)),)
                      for _ in range(modes + 1)] for _ in range(rows)]
            beta = [0] * modes
            for _ in range(rng.randrange(rows + 2)):
                if modes:
                    beta[rng.randrange(modes)] += 1
            self.compare(forms, beta, p)

    def test_extension_and_truncated_rings(self):
        rng = random.Random(2601026)
        rings = [
            RingSpec((1, 1, 1), 1),  # U^2+U+1, irreducible modulo 2.
            RingSpec((1, 1, 1), 3),  # Also retain 1,V,V^2.
            RingSpec((1, 1, 0, 1), 2),  # U^3+U+1.
            RingSpec((0, 0, 1), 2),  # Nonreduced test: irreducibility is unnecessary.
        ]
        for ring in rings:
            for _ in range(100):
                rows = rng.randrange(7)
                modes = rng.randrange(4)
                p = rng.randrange(1, 8)
                forms = [[tuple(rng.randrange(-30, 50) for _ in range(ring.dimension))
                          for _ in range(modes + 1)] for _ in range(rows)]
                beta = [0] * modes
                for _ in range(rng.randrange(rows + 2)):
                    if modes:
                        beta[rng.randrange(modes)] += 1
                self.compare(forms, beta, p, ring)

    def test_precision_is_needed(self):
        # The integer numerator is 2!2! * C(4,2) = 24.
        # Reducing it modulo 8 before division would lose two necessary bits.
        forms = [[(1,), (1,)]] * 4
        result = coefficient_finite_difference(forms, (2,), 3)
        self.assertEqual(result.coefficient, (6,))
        self.assertEqual(result.denominator_valuation, 2)
        self.assertEqual(result.working_precision, 5)
        self.assertEqual(result.evaluation_count, 9)
        self.assertNotEqual(((24 % 8) // 4) % 8, result.coefficient[0])

    def test_binomial_coefficients(self):
        for rows in range(13):
            forms = [[(1,), (1,)]] * rows
            for degree in range(rows + 1):
                result = coefficient_finite_difference(forms, (degree,), 8)
                self.assertEqual(result.coefficient, (comb(rows, degree) % 256,))

    def test_creation_precision_canonical_lifts(self):
        ring = RingSpec((1, 1, 1), 2)
        p = 4
        forms = [[(17, -1, 33, 9), (-2, 18, 8, 31)]] * 5
        canonical = [[tuple(c % (1 << p) for c in a) for a in row] for row in forms]
        a = coefficient_finite_difference(forms, (3,), p, ring)
        b = coefficient_finite_difference(canonical, (3,), p, ring)
        self.assertEqual(a, b)
        self.assertEqual(a.coefficient, coefficient_reference(forms, (3,), p, ring))

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError):
            coefficient_finite_difference([[(1,)]], (1,), 3)
        with self.assertRaises(ValueError):
            coefficient_finite_difference([], (-1,), 3)
        with self.assertRaises(ValueError):
            coefficient_finite_difference([], (), 0)

    @classmethod
    def tearDownClass(cls):
        print(f"\nExact finite-difference/reference comparisons: {cls.comparisons}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
