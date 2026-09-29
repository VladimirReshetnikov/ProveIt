"""Independent unit checks for verify.py; standard library only."""
from __future__ import annotations
from itertools import permutations
from random import Random
import unittest
from verify import (EXPECTED, T64, T75, brute_count, count_three_free,
                    determinant_integer, recurrence_matrix, require)


def determinant_by_definition(matrix: list[list[int]]) -> int:
    """Direct Leibniz sum; deliberately distinct from Bareiss elimination."""
    n = len(matrix)
    total = 0
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = -1 if inversions % 2 else 1
        for i in range(n):
            term *= matrix[i][p[i]]
        total += term
    return total


class VerificationTests(unittest.TestCase):
    def test_empty_permutation(self) -> None:
        self.assertEqual(count_three_free(0), (1, 1))
        self.assertEqual(brute_count(0), 1)

    def test_small_counts(self) -> None:
        for n in range(13):
            with self.subTest(n=n):
                self.assertEqual(count_three_free(n)[0], EXPECTED[n])

    def test_independent_enumeration(self) -> None:
        for n in range(8):
            with self.subTest(n=n):
                self.assertEqual(count_three_free(n)[0], brute_count(n))

    def test_negative_size(self) -> None:
        with self.assertRaises(ValueError):
            count_three_free(-1)

    def test_determinant_boundary_cases(self) -> None:
        cases = [[], [[0]], [[-4]], [[0, 1], [1, 0]],
                 [[1, 2], [2, 4]], [[0, 2, 3], [1, 0, 4], [5, 6, 0]]]
        for matrix in cases:
            with self.subTest(matrix=matrix):
                self.assertEqual(determinant_integer(matrix),
                                 determinant_by_definition(matrix))
        with self.assertRaises(ValueError):
            determinant_integer([[1, 2]])

    def test_determinant_random_exact(self) -> None:
        rng = Random(29092026)
        for n in range(1, 6):
            for sample in range(30):
                matrix = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(n)]
                with self.subTest(n=n, sample=sample):
                    self.assertEqual(determinant_integer(matrix),
                                     determinant_by_definition(matrix))

    def test_matrix_conventions_and_bounds(self) -> None:
        self.assertEqual(recurrence_matrix([1, 2, 3], 1, 0), [[1, 2], [2, 3]])
        with self.assertRaises(ValueError):
            recurrence_matrix([1, 2], 1, 0)

    def test_published_input_separation_arithmetic(self) -> None:
        self.assertGreater((2*T64)**75, (21*T75)**64)
        self.assertGreater((2*T64)*1000**64, 2279**64)
        self.assertLess((21*T75)*500**75, 1139**75)

    def test_explicit_check(self) -> None:
        require(True, 'true condition')
        with self.assertRaises(AssertionError):
            require(False, 'must fail even with Python optimization')


if __name__ == '__main__':
    unittest.main(verbosity=2)
