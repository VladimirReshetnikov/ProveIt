"""Independent checks of the returned certificates.

Run from this directory with:
    python -m unittest -v test_certified_coefficients.py

Small cases use exact Fraction dynamic programming, independently of the
Fourier algorithm.  Astronomical-degree compressed binomials use a separate
high-precision Arb log-gamma identity.  The tests check containment of the
reference in the *exact dyadic endpoints*, not merely overlapping displays.
"""

from fractions import Fraction
import json
import math
import random
import unittest

from flint import arb, ctx, fmpq

from certified_coefficients import (
    CertificationError,
    certify_coefficient,
    certify_probability,
)


def endpoint_fraction(endpoint):
    mantissa = int(endpoint["mantissa"])
    exponent = endpoint["exponent"]
    if exponent >= 0:
        return Fraction(mantissa << exponent)
    return Fraction(mantissa, 1 << (-exponent))


def endpoint_arb(endpoint):
    return arb((int(endpoint["mantissa"]), endpoint["exponent"]))


def probability_dp(probabilities):
    coefficients = [Fraction(1)]
    for p in probabilities:
        updated = [Fraction(0)] * (len(coefficients) + 1)
        for j, coefficient in enumerate(coefficients):
            updated[j] += coefficient * (1 - p)
            updated[j + 1] += coefficient * p
        coefficients = updated
    return coefficients


def polynomial_dp(factors):
    coefficients = [Fraction(1)]
    for a, b in factors:
        updated = [Fraction(0)] * (len(coefficients) + 1)
        for j, coefficient in enumerate(coefficients):
            updated[j] += coefficient * a
            updated[j + 1] += coefficient * b
        coefficients = updated
    return coefficients


class CertifiedCoefficientTests(unittest.TestCase):
    def assert_contains_fraction(self, interval, expected):
        lower, upper = (endpoint_fraction(interval[key]) for key in ("lower", "upper"))
        self.assertLessEqual(lower, expected)
        self.assertLessEqual(expected, upper)

    def assert_relative_width(self, interval, epsilon):
        lower, upper = (endpoint_fraction(interval[key]) for key in ("lower", "upper"))
        self.assertGreater(lower, 0)
        self.assertLessEqual(upper / lower - 1, Fraction(epsilon))

    def assert_contains_reference_ball(self, interval, reference):
        lower, upper = (endpoint_arb(interval[key]) for key in ("lower", "upper"))
        self.assertTrue(lower <= reference.lower())
        self.assertTrue(reference.upper() <= upper)

    def test_exact_fraction_dp_varied_inputs(self):
        generator = random.Random(20261008)
        cases = [
            [Fraction(1, 3), Fraction(2, 5), Fraction(3, 7)],
            [Fraction(1, 10**30), Fraction(1) - Fraction(1, 10**30), Fraction(2, 3)],
            [Fraction(1, 2)] * 12,
        ]
        for _ in range(20):
            n = generator.randint(2, 14)
            cases.append([Fraction(generator.randint(1, 18), 19) for _ in range(n)])
        for probabilities in cases:
            coefficients = probability_dp(probabilities)
            targets = sorted({0, 1, len(probabilities) // 2, len(probabilities) - 1, len(probabilities)})
            for k in targets:
                with self.subTest(n=len(probabilities), k=k, p=probabilities[:2]):
                    result = certify_probability(probabilities, k, "1e-12")
                    self.assertEqual(result["status"], "certified")
                    self.assert_contains_fraction(result["probability"], coefficients[k])
                    self.assert_relative_width(result["probability"], "1e-12")
                    json.dumps(result)

    def test_all_conditional_marginals_against_fraction_dp(self):
        probabilities = [Fraction(0), Fraction(1), Fraction(1, 100), Fraction(2, 7), Fraction(3, 5), Fraction(99, 100)]
        for k in (1, 2, 3, 4, 5):
            mass = probability_dp(probabilities)[k]
            result = certify_probability(probabilities, k, "1e-12", marginals=True)
            for index, p in enumerate(probabilities):
                others = probabilities[:index] + probabilities[index + 1:]
                reference = p * probability_dp(others)[k - 1] / mass
                interval = result["conditional_marginals"][index]
                self.assert_contains_fraction(interval, reference)
                width = endpoint_fraction(interval["upper"]) - endpoint_fraction(interval["lower"])
                self.assertLessEqual(width, Fraction("1e-12"))

    def test_zero_deterministic_and_empty_cases(self):
        self.assertEqual(certify_probability([], 0)["status"], "certified")
        self.assert_contains_fraction(certify_probability([], 0)["probability"], Fraction(1))
        self.assertEqual(certify_probability([], 1)["status"], "zero_probability")
        for k in (-1, 0, 2, 4):
            result = certify_probability([0, 1, 0], k, marginals=True)
            self.assertEqual(result["status"], "zero_probability")
            self.assertIsNone(result["conditional_marginals"])
        result = certify_probability([0, 1, 0], 1, marginals=True)
        self.assert_contains_fraction(result["probability"], Fraction(1))
        for interval, expected in zip(result["conditional_marginals"], (0, 1, 0)):
            self.assert_contains_fraction(interval, Fraction(expected))
        compressed = certify_probability([0, 1], 10**12, multiplicities=[10**9, 10**12])
        self.assert_contains_fraction(compressed["probability"], Fraction(1))

    def test_small_variance_full_grid_branch(self):
        delta = Fraction(1, 10**12)
        probabilities = [delta] * 60 + [1 - delta] * 20
        result = certify_probability(probabilities, 20, "1e-10", marginals=True)
        self.assertTrue(result["stats"]["complete_grid"])
        self.assertEqual(result["stats"]["theta"], "0")
        self.assert_contains_fraction(result["probability"], probability_dp(probabilities)[20])
        self.assert_relative_width(result["probability"], "1e-10")

    def test_rare_binomial_exact_integer_reference(self):
        n, k, p = 1000, 900, Fraction(1, 1000)
        expected = Fraction(math.comb(n, k)) * p**k * (1 - p)**(n - k)
        result = certify_probability([p], k, "1e-12", multiplicities=[n], marginals=True)
        self.assert_contains_fraction(result["probability"], expected)
        self.assert_relative_width(result["probability"], "1e-12")
        self.assert_contains_fraction(result["conditional_marginals"][0], Fraction(k, n))
        self.assertLess(result["stats"]["node_count"], n)

    def test_compressed_degree_trillion_independent_loggamma(self):
        examples = (
            (10**6, 500000, Fraction(1, 2)),
            (10**12, 5 * 10**11, Fraction(1, 2)),
            (10**12, 10**9, Fraction(1, 10**6)),
        )
        for n, k, p in examples:
            with self.subTest(n=n, k=k):
                result = certify_probability([p], k, "1e-12", multiplicities=[n], marginals=True)
                with ctx.workprec(320):
                    p_ball = arb(fmpq(p.numerator, p.denominator))
                    reference = (
                        arb(n + 1).lgamma() - arb(k + 1).lgamma()
                        - arb(n - k + 1).lgamma()
                        + k * p_ball.log() + (n - k) * (1 - p_ball).log()
                    )
                    self.assert_contains_reference_ball(result["log_probability"], reference)
                self.assert_contains_fraction(result["conditional_marginals"][0], Fraction(k, n))
                self.assertEqual(result["stats"]["input_groups"], 1)
                self.assertLessEqual(result["stats"]["node_count"], 128 * math.ceil(math.log(10**15)))
                json.dumps(result)

    def test_compressed_and_general_polynomial_coefficients(self):
        factors = [(Fraction(2), Fraction(3)), (Fraction(4, 7), Fraction(5, 11)), (Fraction(0), Fraction(2))]
        multiplicities = [3, 4, 2]
        expanded = [factor for factor, count in zip(factors, multiplicities) for _ in range(count)]
        coefficients = polynomial_dp(expanded)
        for k in (2, 3, 5, 8, 9):
            result = certify_coefficient(factors, k, "1e-12", multiplicities=multiplicities, marginals=True)
            self.assert_contains_fraction(result["coefficient"], coefficients[k])
            self.assert_relative_width(result["coefficient"], "1e-12")
        zero = certify_coefficient([(1, 2), (0, 0)], 1)
        self.assertEqual(zero["status"], "zero_polynomial")
        self.assertIsNone(zero["probability"])

    def test_compact_endpoints_at_astronomical_binary_scales(self):
        # A Fraction conversion of either output would allocate ~125 GB.
        # Exact Arb dyadics must remain in mantissa/exponent form instead.
        n = 10**12
        probability = certify_probability(["1/2"], 0, "1e-12", multiplicities=[n])
        coefficient = certify_coefficient([(2, 0)], 0, "1e-12", multiplicities=[n])
        with ctx.workprec(320):
            self.assert_contains_reference_ball(probability["probability"], arb((1, -n)))
            self.assert_contains_reference_ball(coefficient["coefficient"], arb((1, n)))
        self.assertLess(len(json.dumps(probability)), 10000)
        self.assertLess(len(json.dumps(coefficient)), 10000)

    def test_precision_adaptation_and_failure_are_honest(self):
        result = certify_probability(["1/3", "2/7", "4/9"], 1, "1e-35", initial_precision=32)
        self.assertGreater(result["stats"]["precision_bits"], 32)
        exact = probability_dp([Fraction(1, 3), Fraction(2, 7), Fraction(4, 9)])[1]
        self.assert_contains_fraction(result["probability"], exact)
        self.assert_relative_width(result["probability"], "1e-35")
        with self.assertRaises(CertificationError):
            certify_probability(["1/3"], 0, "1e-80", initial_precision=32, max_precision=32)

    def test_input_validation(self):
        for invalid in ([0.5], ["-1/2"], ["3/2"]):
            with self.assertRaises((TypeError, ValueError)):
                certify_probability(invalid, 0)
        for epsilon in (0, 1, "-1", "NaN"):
            with self.assertRaises(ValueError):
                certify_probability(["1/2"], 0, epsilon)
        for counts in ([0], [-1], [1.5], [], [1, 2]):
            with self.assertRaises(ValueError):
                certify_probability(["1/2"], 0, multiplicities=counts)
        with self.assertRaises(ValueError):
            certify_coefficient([(-1, 2)], 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
