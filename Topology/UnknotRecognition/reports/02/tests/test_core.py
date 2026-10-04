from __future__ import annotations
from itertools import permutations, product
import json
import random
import subprocess
import sys
import unittest
from unknotlab import Diagram, InvalidDiagram, braid_closure, fox_determinant
from unknotlab.algebra import determinant_bareiss, gf2_rank, integer_nullspace
from unknotlab.khovanov import KhovanovComplex, ResourceLimit, reduced_khovanov
from unknotlab.recognize import parse_input, recognize
from reference import dense_rank, reference_reduced_rank


class DiagramTests(unittest.TestCase):
    def test_empty_means_one_circle(self):
        d = Diagram.from_pd([])
        self.assertEqual(d.crossings, 0)
        self.assertEqual(d.traverse(), ())
        self.assertEqual(d.descending_start(), 0)

    def test_relabel(self):
        d = braid_closure(2, [1, 1, 1])
        e = Diagram.from_pd([[100 * x + 7 for x in c] for c in d.pd])
        self.assertEqual(d, e)

    def test_rotations_preserving_crossing(self):
        d = braid_closure(3, [1, -2] * 2)
        e = Diagram.from_pd([c[2:] + c[:2] for c in reversed(d.pd)])
        self.assertEqual(fox_determinant(e), 5)

    def test_bad_pd(self):
        for pd in [None, 1, [1], [[1, 2, 3]], [[1, 2, 3, 4]],
                   [[True, 2, 2, True]], [[-1, 2, 2, -1]], [[1.0, 2, 2, 1.0]]]:
            with self.subTest(pd=pd), self.assertRaises(InvalidDiagram):
                Diagram.from_pd(pd)

    def test_link_rejected(self):
        for m, word in [(2, []), (2, [1, 1]), (3, [1]), (1, [1]), (10 ** 100, [1])]:
            with self.subTest(m=m, word=word), self.assertRaises(ValueError):
                braid_closure(m, word)

    def test_nonplanar_rotation_rejected(self):
        # This has one component but a positive-genus rotation system.
        with self.assertRaisesRegex(InvalidDiagram, 'Non-planar'):
            Diagram.from_pd([(1, 2, 3, 4), (1, 2, 4, 3)])

    def test_traversal(self):
        d = braid_closure(3, [1, -2] * 2)
        for start in range(16):
            walk = d.traverse(start)
            self.assertEqual(len(walk), 8)
            self.assertEqual(sorted(x // 4 for x in walk), sorted(list(range(4)) * 2))

    def test_braid_errors(self):
        for m, w in [(0, []), (True, []), (2, [0]), (2, [2]), (2, [True])]:
            with self.subTest(m=m, word=w), self.assertRaises(ValueError):
                braid_closure(m, w)


class AlgebraTests(unittest.TestCase):
    def test_determinant_vs_leibniz(self):
        rng = random.Random(1801)
        for n in range(6):
            for _ in range(20):
                matrix = [[rng.randrange(-4, 5) for _ in range(n)] for _ in range(n)]
                expected = 0
                for p in permutations(range(n)):
                    sign = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
                    term = sign
                    for i in range(n):
                        term *= matrix[i][p[i]]
                    expected += term
                self.assertEqual(determinant_bareiss(matrix), expected)

    def test_determinant_validation(self):
        with self.assertRaises(ValueError):
            determinant_bareiss([[1, 2]])

    def test_binary_rank_vs_dense(self):
        rng = random.Random(721)
        for m in range(9):
            for n in range(9):
                a = [[rng.randrange(2) for _ in range(n)] for _ in range(m)]
                packed = [sum(a[i][j] << i for i in range(m)) for j in range(n)]
                self.assertEqual(gf2_rank(packed), dense_rank(a, n))

    def test_binary_rank_validation(self):
        for values in [[-1], [True], [0.5]]:
            with self.assertRaises(ValueError):
                gf2_rank(values)

    def test_integer_kernel(self):
        matrix = [[2, 3, 5, 7], [0, 2, -4, 6]]
        basis = integer_nullspace(matrix, 4)
        self.assertEqual(len(basis), 2)
        for v in basis:
            self.assertTrue(all(sum(a * b for a, b in zip(row, v)) == 0 for row in matrix))
        self.assertEqual(integer_nullspace([], 0), [])
        self.assertEqual(integer_nullspace([], 2), [[1, 0], [0, 1]])
        self.assertEqual(integer_nullspace([[1, 0], [0, 1]], 2), [])

    def test_fox_torus_family(self):
        for n in (1, 3, 5, 7, 9, 21):
            self.assertEqual(fox_determinant(braid_closure(2, [1] * n)), n)

    def test_fox_external_reference_examples(self):
        # Braid words and determinants independently retrieved from Wolfram KnotData.
        for word, determinant in [([1, 1, 2, 2, -1, 2], 7),
                                  ([-1, 2, -1, 3, -2, 3, 2], 9),
                                  ([1, 2, 1, 2, 1, 2, 2, 1], 3),
                                  ([1] + [2] * 5 + [1] + [2] * 3, 1)]:
            self.assertEqual(fox_determinant(braid_closure(max(map(abs, word)) + 1, word)),
                             determinant)


class KhovanovTests(unittest.TestCase):
    def rank(self, m, word):
        return reduced_khovanov(braid_closure(m, word), check_d_squared=True).total_rank

    def test_unknot(self):
        self.assertEqual(self.rank(1, []), 1)
        for sign in (-1, 1):
            self.assertEqual(self.rank(2, [sign]), 1)

    def test_torus_two_strand(self):
        for n in (3, 5, 7):
            self.assertEqual(self.rank(2, [1] * n), n)
            self.assertEqual(self.rank(2, [-1] * n), n)

    def test_figure_eight(self):
        self.assertEqual(self.rank(3, [1, -2] * 2), 5)

    def test_connected_sum(self):
        self.assertEqual(self.rank(3, [1] * 3 + [2] * 3), 9)

    def test_determinant_one_nontrivial(self):
        d = braid_closure(3, [1, 2] * 5)
        self.assertEqual(fox_determinant(d), 1)
        result = reduced_khovanov(d, check_d_squared=True)
        self.assertEqual(result.total_rank, 7)
        self.assertEqual(result.generators, 4209)
        self.assertFalse(result.is_unknot)

    def test_alternate_t35_presentation(self):
        self.assertEqual(self.rank(3, [1] + [2] * 5 + [1] + [2] * 3), 7)

    def test_cancelling_generators(self):
        for i in range(3):
            word = [1, -2] * 2
            word[i:i] = [1, -1]
            self.assertEqual(self.rank(3, word), 5)

    def test_conjugation(self):
        base = [1, -2] * 2
        conjugator = [1, 2]
        inverse = [-g for g in reversed(conjugator)]
        self.assertEqual(self.rank(3, conjugator + base + inverse), 5)

    def test_braid_relation(self):
        suffix = [1]
        d1 = braid_closure(3, [1, 2, 1] + suffix)
        d2 = braid_closure(3, [2, 1, 2] + suffix)
        self.assertEqual(reduced_khovanov(d1).total_rank, reduced_khovanov(d2).total_rank)

    def test_markov_stabilization(self):
        for m, w in [(2, [1] * 3), (3, [1, -2] * 2)]:
            expected = self.rank(m, w)
            for sign in (-1, 1):
                self.assertEqual(self.rank(m + 1, w + [sign * m]), expected)

    def test_relabel_and_marked_arc_independence(self):
        d = braid_closure(3, [1, -2] * 2)
        for shift in range(8):
            e = Diagram.from_pd([[(x + shift) % 8 + 1 for x in c] for c in d.pd])
            self.assertEqual(reduced_khovanov(e).total_rank, 5)

    def test_generator_bound(self):
        for m, word in [(1, []), (2, [1] * 7), (3, [1, 2] * 4)]:
            complex_ = KhovanovComplex(braid_closure(m, word))
            self.assertLessEqual(complex_.generators, 4 ** len(word))

    def test_dense_independent_reference(self):
        rng = random.Random(32026)
        tried = 0
        for n in range(1, 7):
            for _ in range(12):
                word = [rng.choice((-2, -1, 1, 2)) for _ in range(n)]
                try:
                    d = braid_closure(3, word)
                except InvalidDiagram:
                    continue
                tried += 1
                self.assertEqual(reduced_khovanov(d, check_d_squared=True).total_rank,
                                 reference_reduced_rank(d.pd), msg=str(word))
        self.assertGreater(tried, 10)

    def test_resource_guards(self):
        d = braid_closure(3, [1, 2] * 5)
        for kwargs in [{'max_states': 10}, {'max_generators': 10}]:
            with self.subTest(kwargs=kwargs), self.assertRaises(ResourceLimit):
                reduced_khovanov(d, **kwargs)
        for value in (0, -1, True):
            with self.assertRaises(ValueError):
                reduced_khovanov(d, max_states=value)


class RecognitionTests(unittest.TestCase):
    def test_default_positive_and_negative(self):
        positive = recognize(braid_closure(2, [1]))
        negative = recognize(braid_closure(2, [1] * 3))
        self.assertEqual((positive.status, positive.method), ('unknot', 'descending-diagram'))
        self.assertEqual((negative.status, negative.method), ('knotted', 'Fox-determinant'))
        self.assertFalse(negative.as_json()['quasipolynomial_guarantee'])

    def test_real_fallback(self):
        result = recognize(braid_closure(3, [1, 2] * 5))
        self.assertEqual((result.status, result.method), ('knotted', 'reduced-Khovanov-F2'))

    def test_positive_fallback(self):
        d = braid_closure(3, [-2, -2, 1, 2, 2, 2])
        self.assertIsNone(d.descending_start())
        result = recognize(d)
        self.assertEqual((result.status, result.method), ('unknot', 'reduced-Khovanov-F2'))

    def test_fast_unknown(self):
        result = recognize(braid_closure(3, [1, 2] * 5), fast_only=True)
        self.assertEqual(result.status, 'unknown')

    def test_resource_unknown(self):
        result = recognize(braid_closure(3, [1, 2] * 5), max_states=16)
        self.assertEqual(result.status, 'unknown')

    def test_input_validation(self):
        for data in [None, {}, {'pd': [], 'braid': {}}, {'braid': {}},
                     {'braid': {'strands': 2, 'word': None}}]:
            with self.subTest(data=data), self.assertRaises(InvalidDiagram):
                parse_input(data)

    def test_cli(self):
        result = subprocess.run([sys.executable, '-m', 'unknotlab', '-'],
                                input='{"braid":{"strands":2,"word":[1,1,1]}}',
                                text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(result.stdout)['status'], 'knotted')

    def test_cli_unknown(self):
        data = {'braid': {'strands': 3, 'word': [1, 2] * 5}}
        result = subprocess.run([sys.executable, '-m', 'unknotlab', '-', '--fast-only'],
                                input=json.dumps(data), text=True, capture_output=True)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(json.loads(result.stdout)['status'], 'unknown')

    def test_cli_bad_input(self):
        result = subprocess.run([sys.executable, '-m', 'unknotlab', '-'], input='{}',
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 3)
        self.assertEqual(json.loads(result.stdout)['status'], 'invalid-input')

    def test_mutually_exclusive_options(self):
        with self.assertRaises(ValueError):
            recognize(Diagram.from_pd([]), force_homology=True, fast_only=True)
