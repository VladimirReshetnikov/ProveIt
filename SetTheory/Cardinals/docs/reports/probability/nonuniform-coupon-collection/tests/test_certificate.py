"""Independent mathematical checks of the coupon probability certificates.

Run with ``python -m unittest discover -s tests -v`` from the package root.
The reference probabilities use exact rational arithmetic and do not call
the approximation, product-jet, or coefficient-tail implementations.
"""

from __future__ import annotations

import random
import sys
import unittest
from fractions import Fraction
from math import comb, factorial, lcm
from pathlib import Path

from flint import arb, ctx, fmpq

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from coupon_certificate import (  # noqa: E402
    charlier_coefficients,
    coefficient_tails,
    coverage_certificate,
)


def exact_probabilities(weights):
    weights = tuple(Fraction(w) for w in weights)
    total = sum(weights)
    return tuple(w / total for w in weights)


def exact_inclusion_exclusion(weights, m):
    """Integer numerator calculation, with a common exact denominator."""
    weights = tuple(Fraction(w) for w in weights)
    scale = lcm(*(w.denominator for w in weights))
    integers = tuple(int(scale * w) for w in weights)
    total = sum(integers)
    numerator = 0
    for mask in range(1 << len(integers)):
        absent_weight = sum(
            w for i, w in enumerate(integers) if mask & (1 << i)
        )
        term = (total - absent_weight) ** m
        numerator += -term if mask.bit_count() & 1 else term
    return Fraction(numerator, total**m)


def exact_occupancy_dp(weights, m):
    """Exact state-space Markov chain, independent of inclusion-exclusion."""
    probabilities = exact_probabilities(weights)
    states = {0: Fraction(1)}
    for _ in range(m):
        following = {}
        for mask, probability in states.items():
            for i, p in enumerate(probabilities):
                target = mask | (1 << i)
                following[target] = following.get(target, Fraction(0)) + probability * p
        states = following
    return states.get((1 << len(probabilities)) - 1, Fraction(0))


def exact_uniform_occupancy(n, m):
    """Count ordered draw sequences by the number of distinct coupons seen."""
    counts = [1] + [0] * n
    for _ in range(m):
        counts = [0] + [
            k * counts[k] + (n - k + 1) * counts[k - 1]
            for k in range(1, n + 1)
        ]
    return Fraction(counts[n], n**m)


def closed_coefficient(m, k):
    """Binomial-exponential convolution, independent of the code recurrence."""
    return sum(
        (
            Fraction((-1) ** j * comb(m, j) * m ** (k - j), factorial(k - j))
            for j in range(min(m, k) + 1)
        ),
        Fraction(0),
    )


def closed_d_power_coefficient(j, k):
    """Expand [1-(1-x)e^x]^j by two finite binomial sums."""
    return sum(
        (
            Fraction(
                (-1) ** (ell + a) * comb(j, ell) * comb(ell, a)
                * ell ** (k - a),
                factorial(k - a),
            )
            for ell in range(j + 1)
            for a in range(min(ell, k) + 1)
        ),
        Fraction(0),
    )


def rational_ball(value):
    return arb(fmpq(value.numerator, value.denominator))


def direct_subset_reference(weights, m, order, bits=256):
    """Reference moments/approximant by explicit subset summation in Arb."""
    probabilities = exact_probabilities(weights)
    with ctx.workprec(bits):
        moments = [arb(0) for _ in range(3 * order + 1)]
        approximation = arb(0)
        for mask in range(1 << len(probabilities)):
            x = sum(
                (p for i, p in enumerate(probabilities) if mask & (1 << i)),
                Fraction(0),
            )
            exponential = (-m * rational_ball(x)).exp()
            for k in range(3 * order + 1):
                moments[k] += rational_ball(x**k) * exponential
            polynomial = sum(
                (closed_coefficient(m, k) * x**k for k in range(2 * order)),
                Fraction(0),
            )
            summand = rational_ball(polynomial) * exponential
            approximation += -summand if mask.bit_count() & 1 else summand
        return approximation, tuple(moments)


class ExactAlgebraTests(unittest.TestCase):
    def test_charlier_coefficients_against_closed_convolution(self):
        for m in range(0, 13):
            actual = charlier_coefficients(m, 18)
            for k, value in enumerate(actual):
                with self.subTest(m=m, k=k):
                    self.assertEqual(value, closed_coefficient(m, k))

    def test_coefficient_tails_against_closed_expansion(self):
        for order in range(1, 8):
            tails = coefficient_tails(order)
            self.assertEqual(len(tails), order)
            for j in range(1, order):
                expected = 1 - sum(
                    (closed_d_power_coefficient(j, k) for k in range(2 * order)),
                    Fraction(0),
                )
                with self.subTest(order=order, j=j):
                    self.assertEqual(tails[j], expected)
                    self.assertGreaterEqual(expected, 0)
                    self.assertLessEqual(expected, 1)
        self.assertEqual(coefficient_tails(2)[1], Fraction(1, 6))
        self.assertEqual(coefficient_tails(3)[1:], (Fraction(1, 120), Fraction(5, 12)))

    def test_three_exact_probability_representations(self):
        for n in range(1, 7):
            for m in range(1, 15):
                exact = exact_uniform_occupancy(n, m)
                self.assertEqual(exact_inclusion_exclusion([1] * n, m), exact)
                if n <= 4 and m <= 9:
                    self.assertEqual(exact_occupancy_dp([1] * n, m), exact)
        for weights, m in [([1, 2, 3], 7), ([0, 1, 3], 8), ([1, 1, 7, 2], 9)]:
            self.assertEqual(
                exact_occupancy_dp(weights, m), exact_inclusion_exclusion(weights, m)
            )


class CertifiedProbabilityTests(unittest.TestCase):
    def assert_contains_exact(self, certificate, exact):
        rational = fmpq(exact.numerator, exact.denominator)
        self.assertTrue(
            certificate.enclosure.contains(rational),
            f"Exact probability {exact} is outside {certificate.enclosure}",
        )
        self.assertGreaterEqual(exact, 0)
        self.assertLessEqual(exact, 1)

    def test_degenerate_and_low_draw_cases(self):
        # m < order exercises the convention binom(m,j)=0 for j>m.
        cases = [
            ([1], 1, Fraction(1)),
            ([Fraction(7, 13)], 9, Fraction(1)),
            ([1, 0], 4, Fraction(0)),
            ([0, 1, 3, 0], 9, Fraction(0)),
            ([1, 1], 1, Fraction(0)),
            ([1, 2, 3, 4, 5], 3, Fraction(0)),
        ]
        for weights, m, exact in cases:
            self.assertEqual(exact_inclusion_exclusion(weights, m), exact)
            for order in range(1, 6):
                for bits in (64, 160):
                    for grouped in (False, True):
                        with self.subTest(weights=weights, m=m, order=order,
                                          bits=bits, grouped=grouped):
                            result = coverage_certificate(weights, m, order, bits, grouped)
                            self.assert_contains_exact(result, exact)

    def test_uniform_occupancy_probabilities(self):
        for n in (2, 3, 4, 6, 9, 12):
            for m in (1, n, 2 * n, 4 * n):
                exact = exact_uniform_occupancy(n, m)
                for order in range(1, 6):
                    with self.subTest(n=n, m=m, order=order):
                        result = coverage_certificate([1] * n, m, order, 96)
                        self.assert_contains_exact(result, exact)

    def test_seeded_nonuniform_exact_cases(self):
        rng = random.Random(20261008)
        for case in range(60):
            n = rng.randrange(2, 8)
            weights = [Fraction(rng.randrange(0, 13), rng.randrange(1, 8)) for _ in range(n)]
            if not any(weights):
                weights[0] = Fraction(1)
            m = rng.randrange(1, 25)
            exact = exact_inclusion_exclusion(weights, m)
            if case < 8:
                self.assertEqual(exact_occupancy_dp(weights, m), exact)
            for order in range(1, 6):
                bits = (64, 96, 160)[(case + order) % 3]
                with self.subTest(case=case, weights=weights, m=m, order=order, bits=bits):
                    result = coverage_certificate(weights, m, order, bits)
                    self.assert_contains_exact(result, exact)

    def test_grouped_and_ungrouped_enclosures(self):
        cases = [
            ([1] * 7, 19),
            ([1, 1, 2, 2, 2, 9], 17),
            ([Fraction(1, 7)] * 3 + [Fraction(2, 9)] * 4, 23),
            ([0, 0, 1, 1, 2], 3),
        ]
        for weights, m in cases:
            exact = exact_inclusion_exclusion(weights, m)
            for order in range(1, 6):
                grouped = coverage_certificate(weights, m, order, 128, True)
                ungrouped = coverage_certificate(weights, m, order, 128, False)
                self.assert_contains_exact(grouped, exact)
                self.assert_contains_exact(ungrouped, exact)
                for field in ("approximation", "analytic_radius", "poisson", "poisson_missing_mean"):
                    with self.subTest(weights=weights, m=m, order=order, field=field):
                        self.assertTrue(getattr(grouped, field).overlaps(getattr(ungrouped, field)))
                for k, (left, right) in enumerate(zip(grouped.moments, ungrouped.moments)):
                    with self.subTest(order=order, moment=k):
                        self.assertTrue(left.overlaps(right))

    def test_product_jets_against_direct_subset_calculation(self):
        for weights, m in [([1, 2, 6], 13), ([1, 1, 3, 3], 9), ([0, 2, 5], 4)]:
            for order in range(1, 6):
                result = coverage_certificate(weights, m, order, 128)
                reference, moments = direct_subset_reference(weights, m, order)
                with self.subTest(weights=weights, m=m, order=order):
                    self.assertTrue(result.approximation.overlaps(reference))
                for k, (actual, expected) in enumerate(zip(result.moments, moments)):
                    with self.subTest(weights=weights, order=order, moment=k):
                        self.assertTrue(actual.overlaps(expected))

    def test_exact_normalization_and_decimal_inputs(self):
        decimal = coverage_certificate(["0.1", "0.2", "0.3"], 11, 3)
        integers = coverage_certificate([1, 2, 3], 11, 3)
        self.assertTrue(decimal.approximation.overlaps(integers.approximation))
        self.assertTrue(decimal.analytic_radius.overlaps(integers.analytic_radius))
        self.assert_contains_exact(decimal, exact_inclusion_exclusion([1, 2, 3], 11))

    def test_precision_context_restored(self):
        before = ctx.prec
        coverage_certificate([1, 2, 3], 17, 3, bits=192)
        self.assertEqual(ctx.prec, before)

    def test_invalid_inputs(self):
        for weights in ([], [0, 0], [-1, 2]):
            with self.subTest(weights=weights):
                with self.assertRaises(ValueError):
                    coverage_certificate(weights, 3)
        with self.assertRaises(TypeError):
            coverage_certificate([0.1, 0.9], 3)
        for m in (0, -1, Fraction(3, 2)):
            with self.assertRaises(ValueError):
                coverage_certificate([1, 2], m)
        for order in (0, -1, Fraction(3, 2)):
            with self.assertRaises(ValueError):
                coverage_certificate([1, 2], 3, order)
        with self.assertRaises(ValueError):
            coverage_certificate([1, 2], 3, bits=32)


if __name__ == "__main__":
    unittest.main()
