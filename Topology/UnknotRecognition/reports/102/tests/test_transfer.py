import random
import unittest
from cancellation.peeling import column_cancellation_plan
from cancellation.deferred import transport_exact_counts, replay_with_passive


def uncapped_dense(a, moves):
    matrix = {r: {c: v for c, v in row.items() if v} for r, row in a.items()}
    columns = set(c for row in a.values() for c in row)
    for r, c in moves:
        assert matrix[r].get(c) == 1
        donor = matrix.pop(r)
        columns.remove(c)
        for row in matrix.values():
            factor = row.get(c, 0)
            # Read the factor before removing the column; this is an oracle.
            for h in columns:
                row[h] = row.get(h, 0) + factor*donor.get(h, 0)
                if row[h] == 0:
                    del row[h]
            row.pop(c, None)
    return matrix


class TransferTests(unittest.TestCase):
    def test_exact_path_sum(self):
        a = {0: {0: 1, 1: 2, 3: 7}, 1: {1: 1, 2: 3, 3: 5},
             2: {2: 1, 3: 11}, 10: {0: 4, 1: 6, 3: 13}}
        moves = [[0, 0], [1, 1], [2, 2]]
        expected = 13 + 4*7 + (6+4*2)*5 + (6+4*2)*3*11
        self.assertEqual(transport_exact_counts(a, [10], moves), {10: {3: expected}})

    def test_random_exact_and_saturation(self):
        rng = random.Random(81811)
        for _ in range(400):
            u = rng.randrange(1, 9)
            a = {r: {r: 1, **{c: rng.randrange(12) for c in range(r+1, u+3)}}
                 for r in range(u)}
            a[u] = {c: rng.randrange(15) for c in range(u+3)}
            moves = [[r, r] for r in range(u)]
            exact = transport_exact_counts(a, [u], moves)
            self.assertEqual(exact, uncapped_dense(a, moves))
            saturated = {r: {c: min(2, v) for c, v in row.items()} for r, row in exact.items()}
            self.assertEqual(saturated, replay_with_passive(a, [u], moves))

    def test_exponential_value_linear_bits(self):
        u = 4096
        a = {r: {r: 1, u: 1, **({r+1: 2} if r+1 < u else {})} for r in range(u)}
        a[u] = {0: 1}
        moves = [[r, r] for r in range(u)]
        result = transport_exact_counts(a, [u], moves)
        self.assertEqual(result, {u: {u: (1 << u)-1}})
        self.assertEqual(result[u][u].bit_length(), u)

    def test_large_binary_donor(self):
        big = 1 << 8192
        a = {0: {0: 1, 1: big}, 1: {1: 1, 2: big+1}, 2: {0: big-1}}
        result = transport_exact_counts(a, [2], [[0, 0], [1, 1]])
        self.assertEqual(result, {2: {2: (big-1)*big*(big+1)}})

    def test_passive_is_never_dropped(self):
        a = {0: {0: 1}, 1: {0: 3}}
        self.assertEqual(transport_exact_counts(a, [1], [[0, 0]]), {1: {}})


if __name__ == '__main__':
    unittest.main(verbosity=2)
