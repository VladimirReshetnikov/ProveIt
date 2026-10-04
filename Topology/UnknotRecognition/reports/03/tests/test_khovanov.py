import random
import unittest

from unknot_lab.diagrams import PlanarDiagram
from unknot_lab.khovanov import CubeComplex, Limits, ResourceLimit, fox_determinant, recognize


def kh(pd, **kwargs):
    return recognize(pd, check_d2=True, determinant_filter=False, **kwargs)


class KhovanovTests(unittest.TestCase):
    def test_known_knots(self):
        examples = [(2, [1], 1), (2, [1] * 3, 3), (2, [1] * 5, 5),
                    (3, [1, -2] * 2, 5), (3, [1, 2] * 4, 5),
                    (3, [1, 2] * 5, 7)]
        for strands, word, rank in examples:
            with self.subTest(word=word):
                result = kh(PlanarDiagram.from_braid(strands, word))
                self.assertEqual(result["reduced_rank_f2"], rank)
                self.assertEqual(result["is_unknot"], rank == 1)
                self.assertFalse(result["quasipolynomial_guarantee"])

    def test_determinant_one_nontrivial(self):
        pd = PlanarDiagram.from_braid(3, [1, 2] * 5)
        self.assertEqual(fox_determinant(pd), 1)
        result = recognize(pd)
        self.assertEqual(result["method"], "reduced-khovanov-F2")
        self.assertFalse(result["is_unknot"])

    def test_determinant_filter(self):
        for strands, word, determinant in [(2, [1] * 3, 3), (3, [1, -2] * 2, 5)]:
            result = recognize(PlanarDiagram.from_braid(strands, word))
            self.assertEqual(result["determinant"], determinant)
            self.assertEqual(result["method"], "fox-determinant-obstruction")
            self.assertFalse(result["is_unknot"])

    def test_knot_atlas_trefoil(self):
        pd = PlanarDiagram.from_pd([[1, 4, 2, 5], [3, 6, 4, 1], [5, 2, 6, 3]])
        self.assertEqual(kh(pd)["reduced_rank_f2"], 3)

    def test_basepoint_independence(self):
        pd = PlanarDiagram.from_braid(3, [1, -2] * 2)
        for label in pd.labels:
            self.assertEqual(kh(pd, basepoint_label=label)["reduced_rank_f2"], 5)

    def test_mirror(self):
        for word in [[1, 1, 1], [1, -2] * 2, [1, 2] * 4]:
            strands = 1 + max(map(abs, word))
            a = kh(PlanarDiagram.from_braid(strands, word))["reduced_rank_f2"]
            b = kh(PlanarDiagram.from_braid(strands, [-g for g in word]))["reduced_rank_f2"]
            self.assertEqual(a, b)

    def test_relabel_reorder_and_halfturn(self):
        pd = PlanarDiagram.from_braid(3, [1, -2] * 2)
        rows = [[100 + 7 * e for e in row] for row in pd.crossings]
        transformed = [row[2:] + row[:2] for row in reversed(rows)]
        self.assertEqual(kh(PlanarDiagram.from_pd(transformed))["reduced_rank_f2"], 5)

    def test_inverse_generator_pairs(self):
        for prefix in [[1, 2], [1, -2] * 2]:
            expected = kh(PlanarDiagram.from_braid(3, prefix))["reduced_rank_f2"]
            for g in [1, -1, 2, -2]:
                word = prefix[:1] + [g, -g] + prefix[1:]
                self.assertEqual(kh(PlanarDiagram.from_braid(3, word))["reduced_rank_f2"],
                                 expected)

    def test_markov_stabilizations(self):
        for strands, word in [(2, [1]), (2, [1] * 3), (3, [1, -2] * 2)]:
            expected = kh(PlanarDiagram.from_braid(strands, word))["reduced_rank_f2"]
            for sign in [-1, 1]:
                pd = PlanarDiagram.from_braid(strands + 1, word + [sign * strands])
                self.assertEqual(kh(pd)["reduced_rank_f2"], expected)

    def test_braid_relation(self):
        a = PlanarDiagram.from_braid(3, [1, 2, 1, 2])
        b = PlanarDiagram.from_braid(3, [2, 1, 2, 2])
        self.assertEqual(kh(a)["reduced_rank_f2"], kh(b)["reduced_rank_f2"])

    def test_seeded_conjugated_unknots(self):
        rng = random.Random(20260917)
        for _ in range(24):
            prefix = [rng.choice([-2, -1, 1, 2]) for _ in range(3)]
            inverse = [-g for g in reversed(prefix)]
            word = prefix + [rng.choice([-1, 1]), rng.choice([-2, 2])] + inverse
            pd = PlanarDiagram.from_braid(3, word)
            self.assertEqual(fox_determinant(pd), 1)
            self.assertEqual(kh(pd)["reduced_rank_f2"], 1)

    def test_crossing_free_and_curls(self):
        self.assertTrue(kh(PlanarDiagram.from_pd([]))["is_unknot"])
        for row in [[1, 1, 2, 2], [1, 2, 2, 1], [2, 1, 1, 2], [2, 2, 1, 1]]:
            self.assertEqual(kh(PlanarDiagram.from_pd([row]))["reduced_rank_f2"], 1)

    def test_limits_do_not_answer_no(self):
        pd = PlanarDiagram.from_braid(3, [1, 2])
        for limits in [Limits(states=2), Limits(generators=1), Limits(matrix_bits=1)]:
            with self.subTest(limits=limits), self.assertRaises(ResourceLimit):
                recognize(pd, limits)

    def test_all_resolutions_enumerated(self):
        for n in range(1, 8):
            pd = PlanarDiagram.from_braid(n + 1, list(range(1, n + 1)))
            result = kh(pd)
            self.assertEqual(result["resolutions"], 2 ** n)
            self.assertEqual(result["chain_generators"], 3 ** n)
            self.assertTrue(result["is_unknot"])


if __name__ == "__main__":
    unittest.main()
