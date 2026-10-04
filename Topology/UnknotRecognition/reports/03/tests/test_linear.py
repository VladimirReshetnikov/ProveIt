import itertools
import random
import unittest
from fractions import Fraction

from unknot_lab.linear import determinant_bareiss, rank_f2


def slow_rank(columns, rows):
    a = [[(col >> r) & 1 for col in columns] for r in range(rows)]
    rank = 0
    for c in range(len(columns)):
        p = next((r for r in range(rank, rows) if a[r][c]), None)
        if p is None:
            continue
        a[rank], a[p] = a[p], a[rank]
        for r in range(rank + 1, rows):
            if a[r][c]:
                a[r] = [x ^ y for x, y in zip(a[r], a[rank])]
        rank += 1
    return rank


def rational_det(matrix):
    n = len(matrix)
    a = [list(map(Fraction, row)) for row in matrix]
    determinant = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if a[r][c]), None)
        if p is None:
            return 0
        if p != c:
            a[c], a[p] = a[p], a[c]
            determinant *= -1
        determinant *= a[c][c]
        pivot = a[c][c]
        a[c] = [x / pivot for x in a[c]]
        for r in range(c + 1, n):
            factor = a[r][c]
            a[r] = [x - factor * y for x, y in zip(a[r], a[c])]
    return determinant


class LinearTests(unittest.TestCase):
    def test_exhaustive_three_by_three_ranks(self):
        for columns in itertools.product(range(8), repeat=3):
            self.assertEqual(rank_f2(columns), slow_rank(columns, 3))

    def test_random_ranks(self):
        rng = random.Random(20260917)
        for _ in range(100):
            rows, cols = rng.randrange(1, 15), rng.randrange(1, 15)
            columns = [rng.getrandbits(rows) for _ in range(cols)]
            self.assertEqual(rank_f2(columns), slow_rank(columns, rows))

    def test_bareiss_against_rational_elimination(self):
        rng = random.Random(17)
        for n in range(7):
            for _ in range(20):
                a = [[rng.randrange(-5, 6) for _ in range(n)] for _ in range(n)]
                self.assertEqual(determinant_bareiss(a), rational_det(a))

    def test_invalid(self):
        with self.assertRaises(ValueError):
            rank_f2([-1])
        with self.assertRaises(ValueError):
            determinant_bareiss([[1, 2]])


if __name__ == "__main__":
    unittest.main()
