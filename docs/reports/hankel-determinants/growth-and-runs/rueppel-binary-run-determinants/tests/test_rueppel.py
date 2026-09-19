"""Independent small-size tests, including arbitrary matrices and reciprocal minors."""
import itertools
import pathlib
import random
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'code'))
import rueppel as r


def permutation_determinant(a):
    n = len(a)
    total = 0
    for p in itertools.permutations(range(n)):
        term = r.sign(sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)))
        for i in range(n):
            term *= a[i][p[i]]
        total += term
    return total


class ExactTests(unittest.TestCase):
    def test_bareiss_against_leibniz(self):
        rng = random.Random(20260919)
        for n in range(7):
            for _ in range(20):
                a = [[rng.randrange(-3, 4) for _ in range(n)] for _ in range(n)]
                self.assertEqual(r.determinant(a), permutation_determinant(a))

    def test_reciprocal_complementary_minors(self):
        rng = random.Random(42)
        for _ in range(12):
            a = [1] + [rng.randrange(-2, 3) for _ in range(30)]
            c = r.reciprocal_coefficients(a)
            for n in range(1, 5):
                for s in range(1, 6):
                    lhs = r.hankel(c, n, s)
                    rhs = r.sign(n + (s - 1) * (s - 2) // 2) * r.hankel(a, n + s - 1, 2 - s)
                    self.assertEqual(lhs, rhs)
            for n in range(1, 8):
                self.assertEqual(r.hankel(c, n), r.sign(n - 1) * r.hankel(a, n - 1, 2))

    def test_binary_statistics(self):
        for n in range(2000):
            bits = bin(n)[2:] if n else ''
            runs = sum(j == 0 or bits[j] != bits[j - 1] for j in range(len(bits)))
            ones = sum(bit == '1' and (j == 0 or bits[j - 1] == '0')
                       for j, bit in enumerate(bits))
            self.assertEqual(r.binary_runs(n), runs)
            self.assertEqual(r.one_runs(n), ones)
            self.assertEqual(r.E(n), r.E_by_recursion(n))

    def test_families(self):
        moments = [r.rueppel(j) for j in range(60)]
        for n in range(16):
            self.assertEqual(r.hankel(moments, n), r.D(n))
            self.assertEqual(r.hankel(moments, n, 1), r.E(n))
            self.assertEqual(r.hankel(moments, n, 2), r.T(n))
            self.assertEqual(r.hankel(moments, n, -1), r.B(n))
            for t in (-3, -1, 0, 1, 2):
                self.assertEqual(r.hankel(r.parameter_moments(60, t), n), r.parameter_hankel(n, t))
                self.assertEqual(r.hankel(r.periodic_moments(60, 2, t), n), r.periodic_hankel(n, 2, t))
                linear = r.linear_moments(60, 1, t)
                self.assertEqual(r.hankel(linear, n), r.linear_hankel(n, 1, t))
                inverse = r.reciprocal_coefficients(linear)
                self.assertEqual(r.hankel(inverse, n), r.reciprocal_hankel(n, t))

    def test_bad_inputs(self):
        for n in (-1, 1.5, True):
            with self.assertRaises(ValueError):
                r.binary_runs(n)
        with self.assertRaises(ValueError):
            r.determinant([[1, 2]])
        with self.assertRaises(ValueError):
            r.hankel([1], 2)
        with self.assertRaises(ValueError):
            r.reciprocal_coefficients([2, 1])


if __name__ == '__main__':
    unittest.main(verbosity=2)
