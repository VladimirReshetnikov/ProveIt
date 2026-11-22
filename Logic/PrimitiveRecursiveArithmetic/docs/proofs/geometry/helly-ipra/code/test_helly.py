"""Run with python -m unittest -v test_helly in this directory."""

from dataclasses import replace
from fractions import Fraction as Q
from itertools import combinations
from unittest import TestCase, main

from helly import Certificate, helly, radon_weights, sparsify, verify


def omission_table(points):
    return {tuple(j for j in range(len(points)) if j != i): point
            for i, point in enumerate(points)}


class HellyTests(TestCase):
    def checked(self, d, n, local, compact=False):
        certificate = helly(d, n, local, compact=compact)
        self.assertTrue(verify(d, n, local, certificate))
        if compact:
            self.assertTrue(all(len(row) <= d + 1 for row in certificate.rows))
        return certificate

    def test_empty_family(self):
        for d in (0, 1, 4):
            self.assertEqual(self.checked(d, 0, {}).point, (0,) * d)
        self.checked(4, 0, {(): (7, 0, 8, 1)})

    def test_zero_dimension(self):
        local = {(i,): () for i in range(6)}
        c = self.checked(0, 6, local, compact=True)
        self.assertEqual(c.point, ())
        for i, row in enumerate(c.rows):
            self.assertEqual(row, {(i,): 1})

    def test_small_family(self):
        local = {(0, 1): (1, 2, 3, 4, 5)}
        c = self.checked(5, 2, local)
        self.assertEqual(c.point, local[0, 1])
        self.assertEqual(c.rows, ({(0, 1): 1}, {(0, 1): 1}))

    def test_rational_median(self):
        local = omission_table([(Q(3, 7),), (-2,), (Q(5, 4),)])
        self.assertEqual(self.checked(1, 3, local).point, (Q(3, 7),))

    def test_square(self):
        local = omission_table([(0, 0), (2, 0), (2, 2), (0, 2)])
        c = self.checked(2, 4, local)
        self.assertEqual(c.point, (1, 1))
        for row in c.rows:
            self.assertEqual(sorted(row.values()), [Q(1, 2), Q(1, 2)])

    def test_repeated_collinear_coplanar_points(self):
        for points in (
                [(1, 1)] * 4,
                [(0, 5), (0, 5), (7, 5), (9, 5)],
                [(0, 0, 1), (2, 0, 1), (2, 2, 1), (0, 2, 1), (0, 0, 1)]):
            self.checked(len(points[0]), len(points), omission_table(points))

    def test_more_than_d_plus_two(self):
        # The omitted indices exclude at least one member of the parent subset.
        d, n = 2, 7
        local = {t: (Q((i * 41 + 3) % 17, 13), Q((i * i + 15) % 31, 11))
                 for i, t in enumerate(combinations(range(n), d + 1))}
        c = self.checked(d, n, local)
        sparse = self.checked(d, n, local, compact=True)
        self.assertEqual(c.point, sparse.point)

    def test_carathéodory_reduction(self):
        points = {(0,): (0, 0), (1,): (4, 0), (2,): (4, 4), (3,): (0, 4),
                  (4,): (1, 3), (5,): (0, 0)}
        row = {t: Q(1, 6) for t in points}
        small = sparsify(2, points, row)
        self.assertLessEqual(len(small), 3)
        self.assertTrue(all(w > 0 for w in small.values()))
        self.assertEqual(sum(small.values()), 1)
        for k in range(2):
            self.assertEqual(sum(w * points[t][k] for t, w in small.items()),
                             sum(w * points[t][k] for t, w in row.items()))

    def test_radon_disjointness(self):
        for pts in ([(), ()], [(0, 0), (2, 0), (2, 2), (0, 2)],
                    [(1, 2, 3)] * 5):
            a, b = radon_weights(pts)
            self.assertEqual(sum(a), 1)
            self.assertEqual(sum(b), 1)
            self.assertTrue(all(u >= 0 and v >= 0 and u * v == 0 for u, v in zip(a, b)))
            for k in range(len(pts[0])):
                self.assertEqual(sum(w * p[k] for w, p in zip(a, pts)),
                                 sum(w * p[k] for w, p in zip(b, pts)))

    def test_checker_rejects_corruptions(self):
        # All seeds coincide, so bad incidence still passes the point equation.
        local = omission_table([(0,), (0,), (0,)])
        c = self.checked(1, 3, local)
        self.assertFalse(verify(1, 3, local, replace(c, rows=({(1, 2): 1},) + c.rows[1:])))
        self.assertFalse(verify(1, 3, local, replace(c, rows=({(0, 1): -1, (0, 2): 2},) + c.rows[1:])))
        self.assertFalse(verify(1, 3, local, replace(c, rows=({(0, 1): Q(1, 2)},) + c.rows[1:])))
        self.assertFalse(verify(1, 3, local, replace(c, point=(1,))))
        self.assertFalse(verify(1, 3, local, Certificate((0,), ())))
        self.assertFalse(verify(1, 3, {(0, 1): (0,)}, c))

    def test_invalid_input(self):
        with self.assertRaises(ValueError):
            helly(1, 3, {(0, 1): (0,)})
        with self.assertRaises(ValueError):
            helly(1, 1, {(0,): (0.5,)})
        with self.assertRaises(ValueError):
            helly(1, 1, {(0,): (0, 0)})


if __name__ == "__main__":
    main()
