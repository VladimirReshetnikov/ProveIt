"""Executable diagnostic checks for the finite identities in the article.

Run from the package root with: python3 -m unittest discover -s tests -v
These checks do not certify a universal theorem and are not Lean proofs.
"""

import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "artifacts"))
import finite_sieve as fs


class FiniteSieveTests(unittest.TestCase):
    def test_factorization_and_mobius(self):
        for n in range(1, 200):
            reconstructed = 1
            for p, e in fs.factor(n):
                self.assertTrue(fs.is_prime(p))
                reconstructed *= p ** e
            self.assertEqual(reconstructed, n)
            divisor_sum = sum(fs.mobius(d) for d in range(1, n + 1) if n % d == 0)
            self.assertEqual(divisor_sum, int(n == 1))

    def test_root_counts(self):
        for d in range(1, 80):
            if fs.squarefree(d):
                self.assertEqual(len(fs.root_residues(d)), fs.rho(d))

    def test_sieve_inversion_and_normalization(self):
        for z in range(1, 25):
            data = fs.sieve_data(z)
            self.assertEqual(data.lam[1], 1)
            for r in data.divisors:
                recovered = sum(data.lam[d] * fs.g(d) for d in data.divisors if d % r == 0)
                self.assertEqual(recovered, data.y[r])
                self.assertLessEqual(abs(data.lam[r]) * fs.rho(r), r)

    def test_diagonal_identity(self):
        for z in range(1, 25):
            data = fs.sieve_data(z)
            self.assertEqual(fs.quadratic_form(data), 1 / data.G)
            for d in data.divisors:
                for e in data.divisors:
                    identity_rhs = fs.g(d) * fs.g(e) * sum(
                        1 / fs.h(r) for r in data.divisors if d % r == 0 and e % r == 0
                    )
                    self.assertEqual(fs.g(fs.lcm(d, e)), identity_rhs)

    def test_radical_grouping(self):
        for s in range(1, 13):
            masses = fs.radical_pair_masses(s)
            self.assertEqual(sum(masses.values()), fs.harmonic(s) ** 2)
            for d, mass in masses.items():
                self.assertLessEqual(mass, (3 if d % 2 == 0 else 1) * fs.h(d))

    def test_harmonic_lower_bound(self):
        for t in range(8):
            self.assertGreaterEqual(fs.harmonic(2 ** t), 1 + Fraction(t, 2))
        for s in range(1, 13):
            G = sum(fs.h(d) for d in range(1, s * s + 1) if fs.squarefree(d))
            self.assertLessEqual(fs.harmonic(s) ** 2, 3 * G)

    def test_finite_sieve_majorant(self):
        for z in range(1, 13):
            data = fs.sieve_data(z)
            for X in (1, 7, 30, 100):
                square_sum = fs.weighted_square_sum(X, data)
                self.assertLessEqual(fs.sifted_count(X, z), square_sum)
                self.assertLessEqual(abs(square_sum - Fraction(X) / data.G), z ** 4)
                self.assertLessEqual(fs.twin_count(X), z + Fraction(X) / data.G + z ** 4)

    def test_bruns_sum_convention_and_integer_code(self):
        self.assertEqual(fs.brun_partial_sum(4), Fraction(1, 3) + Fraction(1, 5))
        self.assertEqual(fs.brun_partial_sum(6), Fraction(1, 3) + 2 * Fraction(1, 5) + Fraction(1, 7))
        self.assertEqual(fs.brun_partial_sum(8), Fraction(92, 105))
        for N in range(80):
            A, D = fs.brun_integer_code(N)
            self.assertEqual(Fraction(A, D), fs.brun_partial_sum(N))

    def test_symbolic_cutoff(self):
        self.assertEqual(fs.cutoff_description(0), "2^(2^(0+13))")
        self.assertEqual(fs.cutoff_description(1000), "2^(2^(1000+13))")

    def test_full_diagnostic_report(self):
        report = fs.verification_report()
        self.assertEqual(report["status"], "PASS")
        self.assertGreater(report["total_assertions"], 1000)


if __name__ == "__main__":
    unittest.main()
