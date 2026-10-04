import random
import unittest

from unknot.linear import apply_matrix, rank_f2, set_bits


def dense_rank(columns, rows):
    matrix = [[(c >> i) & 1 for c in columns] for i in range(rows)]
    r = 0
    for j in range(len(columns)):
        pivot = next((i for i in range(r, rows) if matrix[i][j]), None)
        if pivot is None:
            continue
        matrix[r], matrix[pivot] = matrix[pivot], matrix[r]
        for i in range(rows):
            if i != r and matrix[i][j]:
                matrix[i] = [a ^ b for a, b in zip(matrix[i], matrix[r])]
        r += 1
    return r


class LinearTests(unittest.TestCase):
    def test_dense_comparison_360_matrices(self):
        random_ = random.Random(71623)
        for rows in range(12):
            for cols in range(10):
                for trial in range(3):
                    data = [random_.getrandbits(rows) for _ in range(cols)]
                    self.assertEqual(rank_f2(data, rows), dense_rank(data, rows))

    def test_basis_and_dependence(self):
        self.assertEqual(rank_f2([1, 2, 4, 7], 3), 3)
        self.assertEqual(rank_f2([3, 3, 0], 2), 1)
        self.assertEqual(rank_f2([], 0), 0)

    def test_linear_application(self):
        self.assertEqual(apply_matrix([3, 6, 1], 0b101), 2)
        self.assertEqual(list(set_bits(0b101010)), [1, 3, 5])

    def test_validation(self):
        for data, rows in [([-1], 2), ([8], 3), ([True], 1), ([1], -1), ([0], True)]:
            with self.subTest(data=data, rows=rows), self.assertRaises(ValueError):
                rank_f2(data, rows)
        with self.assertRaises(ValueError):
            apply_matrix([1], 2)
        with self.assertRaises(ValueError):
            list(set_bits(-1))


if __name__ == '__main__':
    unittest.main()
