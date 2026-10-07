"""Independent finite-field and integration checks for sparse determinants."""
import itertools
import random
import unittest

from fastunknot import Diagram, DiagramError
from fastunknot.filters import alexander_obstruction, determinant_mod
from fastunknot.sparse import sparse_determinant


def leibniz(matrix, p):
    n = len(matrix)
    result = 0
    for perm in itertools.permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        term = -1 if inversions % 2 else 1
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        result += term
    return result % p


def sparse_rows(matrix):
    return [{j: x for j, x in enumerate(row) if x} for row in matrix]


class SparseDeterminantTests(unittest.TestCase):
    def test_against_independent_leibniz(self):
        rng = random.Random(707)
        for n in range(6):
            for p in (2, 3, 101):
                for _ in range(25):
                    a = [[rng.randrange(p) if rng.randrange(3) == 0 else 0
                          for _ in range(n)] for _ in range(n)]
                    self.assertEqual(sparse_determinant(sparse_rows(a), p=p), leibniz(a, p))

    def test_against_dense_random_and_singular(self):
        rng = random.Random(8173)
        for n in (1, 2, 3, 5, 10, 21, 50):
            for p in (2, 7, 101, (1 << 61)-1):
                for k in range(15):
                    a = [[rng.randrange(p) if rng.random() < 0.22 else 0
                          for _ in range(n)] for _ in range(n)]
                    if k % 3 == 0 and n > 1:
                        a[-1] = a[0][:]
                    expected = determinant_mod(a, p)
                    rows = sparse_rows(a)
                    before = [r.copy() for r in rows]
                    stats = {}
                    self.assertEqual(sparse_determinant(rows, p=p, stats=stats), expected)
                    self.assertEqual(rows, before)
                    self.assertLessEqual(stats['fill_created'], stats['schur_updates'])

    def test_permutation_signs_and_long_sparse_case(self):
        rng = random.Random(21)
        for n in (20, 100, 1000):
            perm = list(range(n))
            rng.shuffle(perm)
            odd = sum(perm[i] > perm[j] for i in range(n) for j in range(i+1,n)) % 2
            stats = {}
            self.assertEqual(sparse_determinant([{j:1} for j in perm], p=101, stats=stats),
                             100 if odd else 1)
            self.assertEqual(stats['schur_updates'], 0)

    def test_resource_callback_and_validation(self):
        class Stop(Exception):
            pass
        def stop():
            raise Stop
        with self.assertRaises(Stop):
            sparse_determinant([{0:1}], check=stop)
        for rows, n in (([{1:1}], 1), ([{0:1}], 2), ([{-1:1}], 1)):
            with self.assertRaises(ValueError):
                sparse_determinant(rows, n=n)

    def test_transient_nonzero_peak(self):
        rows = [{0: 1, 1: 1, 2: 1, 3: 1}, {0: 1, 3: 1, 4: 1, 5: 1}]
        rows += [{1: 1, 2: 1, 4: 1, 5: 1} for _ in range(4)]
        stats = {}
        self.assertEqual(sparse_determinant(rows, p=101, stats=stats), 0)
        self.assertEqual(stats["initial_nonzeros"], 24)
        # First pivot: remove (1,0), create (1,1) and (1,2), then cancel (1,3).
        # The counts 24 -> 23 -> 24 -> 25 -> 24 expose a transient cell peak.
        self.assertEqual(stats["peak_nonzeros"], 25)

    def test_alexander_evidence_matches_dense(self):
        rng = random.Random(829)
        done = 0
        while done < 120:
            strands = rng.randrange(2, 7)
            word = [rng.choice((-1,1)) * rng.randrange(1,strands)
                    for _ in range(rng.randrange(1,40))]
            try:
                diagram = Diagram.from_braid(strands,word)
            except DiagramError:
                continue
            self.assertEqual(alexander_obstruction(diagram, backend='dense'),
                             alexander_obstruction(diagram, backend='sparse'))
            done += 1
        for q in (61, 127, 257):
            diagram = Diagram.from_braid(3, [1,2]*q)
            self.assertEqual(alexander_obstruction(diagram, backend='dense'),
                             alexander_obstruction(diagram, backend='sparse'))


if __name__ == '__main__':
    unittest.main()
