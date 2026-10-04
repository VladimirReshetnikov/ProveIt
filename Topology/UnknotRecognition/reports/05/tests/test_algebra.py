import itertools
import random
import unittest
from fractions import Fraction

from unknot_recognition.algebra import bareiss_determinant, rank_f2, rational_nullspace


def permutation_determinant(a):
    n = len(a)
    total = 0
    for perm in itertools.permutations(range(n)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        term = sign
        for i, j in enumerate(perm):
            term *= a[i][j]
        total += term
    return total


def dense_f2_rank(columns, rows):
    matrix = [[(column >> row) & 1 for column in columns] for row in range(rows)]
    rank = 0
    for j in range(len(columns)):
        pivot = next((i for i in range(rank, rows) if matrix[i][j]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for i in range(rows):
            if i != rank and matrix[i][j]:
                matrix[i] = [a ^ b for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


class AlgebraTests(unittest.TestCase):
    def test_bareiss_exhaustive_small(self):
        for entries in itertools.product((-1, 0, 1), repeat=4):
            a = [list(entries[:2]), list(entries[2:])]
            self.assertEqual(bareiss_determinant(a), permutation_determinant(a))

    def test_bareiss_random(self):
        rng = random.Random(20260917)
        for n in range(6):
            for _ in range(12):
                a = [[rng.randrange(-5, 6) for _ in range(n)] for _ in range(n)]
                self.assertEqual(bareiss_determinant(a), permutation_determinant(a))

    def test_bareiss_big_integer(self):
        x = 1 << 400
        self.assertEqual(bareiss_determinant([[x, x + 1], [x - 1, x]]), 1)

    def test_bareiss_invalid(self):
        for a in ([[1, 2]], [[True]], [[Fraction(1, 2)]]):
            with self.assertRaises((ValueError, TypeError)):
                bareiss_determinant(a)

    def test_bit_rank_against_dense(self):
        rng = random.Random(981)
        for rows in range(10):
            for columns in range(12):
                a = [rng.randrange(1 << rows) for _ in range(columns)]
                self.assertEqual(rank_f2(a), dense_f2_rank(a, rows))

    def test_nullspace_integrality(self):
        matrix = [[2, 3, 1, 0], [4, 6, 2, 0], [0, 0, 0, 0]]
        basis = rational_nullspace(matrix, 4)
        self.assertEqual(len(basis), 3)
        for v in basis:
            self.assertTrue(all(type(x) is int for x in v))
            self.assertTrue(all(sum(x * y for x, y in zip(row, v)) == 0 for row in matrix))

    def test_empty_nullspace(self):
        self.assertEqual(len(rational_nullspace([], 3)), 3)
        self.assertEqual(len(rational_nullspace([[1, 0], [0, 1]], 2)), 0)


if __name__ == '__main__':
    unittest.main()
