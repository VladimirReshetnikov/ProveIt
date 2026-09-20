"""Boundary and input-validation tests; run directly with Python 3.10+."""
import unittest
from kbonacci_parity import (
    CoefficientOracle, coherent_signs, count_fast, count_prefix,
    parity_bitset, signed_sparse, standard_seeds, weights,
)


class APIBoundaryTests(unittest.TestCase):
    def test_empty_product(self):
        for k in range(2, 8):
            oracle = CoefficientOracle(k, 0)
            self.assertEqual(count_fast(k, 0), 1)
            self.assertEqual(count_prefix(k, 0), [1])
            self.assertEqual(oracle.signed(0), 1)
            self.assertEqual(oracle.signed(-1), 0)
            self.assertEqual(oracle.signed(1), 0)
            self.assertEqual(parity_bitset([]), 1)

    def test_first_overlap(self):
        for k in range(2, 9):
            a = weights(k, k+1)
            self.assertEqual(CoefficientOracle(k, k+1).signed(a[-1]), 0)
            self.assertEqual(count_fast(k, k+1), 2**(k+1)-2)

    def test_custom_gaps_and_signs(self):
        k, n, seeds, initial = 3, 10, [2, 7, 15], [-1, 1, -1]
        a, e = weights(k, n, seeds), coherent_signs(k, n, initial)
        oracle = CoefficientOracle(k, n, seeds, initial)
        direct = signed_sparse(a, e)
        for m in range(-1, sum(a)+2):
            self.assertEqual(oracle.signed(m), direct.get(m, 0))
        self.assertEqual(len(direct), count_fast(k, n))

    def test_composite_moduli(self):
        for k in range(2, 8):
            exact = count_prefix(k, 100)
            for modulus in (1, 2, 4, 6, 12, 1000):
                self.assertEqual(count_prefix(k, 100, modulus),
                                 [x % modulus for x in exact])
                for n in (0, 1, k, k+1, 99, 100):
                    self.assertEqual(count_fast(k, n, modulus), exact[n] % modulus)

    def test_invalid_orders_indices_and_moduli(self):
        for k in (-1, 0, 1, True, 2.5):
            with self.assertRaises(ValueError):
                count_fast(k, 10)
        for n in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                count_fast(3, n)
        for modulus in (0, -1, True, 2.5):
            with self.assertRaises(ValueError):
                count_fast(3, 10, modulus)

    def test_seed_validation(self):
        for seeds in ([1, 2, 3], [1, 1, 4], [0, 2, 4], [1.0, 3, 5],
                      [True, 3, 5], [1, 3]):
            with self.assertRaises(ValueError):
                weights(3, 10, seeds)
        self.assertEqual(standard_seeds(3), [1, 3, 5])

    def test_sign_validation(self):
        for initial in ([1, 1], [1, 1, 0], [1, 1, True], [1, 1, 1.0]):
            with self.assertRaises(ValueError):
                coherent_signs(3, 10, initial)
        for sign in (0, 2, True, 1.0):
            with self.assertRaises(ValueError):
                signed_sparse([1], [sign])

    def test_degree_cap_and_query_validation(self):
        with self.assertRaises(ValueError):
            parity_bitset([2, 3], max_degree=4)
        with self.assertRaises(ValueError):
            parity_bitset([0])
        oracle = CoefficientOracle(3, 8)
        for m in (True, 1.5):
            with self.assertRaises(ValueError):
                oracle.signed(m)
        self.assertEqual(oracle.signed(105), -1)
        self.assertEqual(oracle.parity(105), 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
