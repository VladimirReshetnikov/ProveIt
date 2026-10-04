import random
import unittest

from unknot_recognition import InvalidDiagram, PlanarDiagram, braid_closure, read_diagram, recognize
from unknot_recognition.determinant import knot_determinant
from unknot_recognition.khovanov import ReducedComplex, ResourceLimit
from unknot_recognition.reduction import legal_reductions, simplify, verify_reduction_trace


class DiagramTests(unittest.TestCase):
    def test_empty_is_one_circle(self):
        self.assertEqual(read_diagram({'pd': []}).n, 0)
        self.assertEqual(braid_closure(1, []).n, 0)

    def test_braid_input_validation(self):
        for m, w in ((2, []), (2, [1, 1]), (3, [1]), (2, [0]), (2, [2]),
                     (2, [True]), (0, []), (2, None), (1000000, [])):
            with self.subTest(strands=m, word=w), self.assertRaises(InvalidDiagram):
                braid_closure(m, w)

    def test_pd_input_validation(self):
        for data in (None, {}, {'pd': [], 'braid': {}}, {'pd': [[1, 2, 3]]},
                     {'pd': [[1, 2, 3, 4]]}, {'pd': [[True, True, 1, 1]]},
                     {'pd': [[0, 1, 0, 1]]}):
            with self.subTest(data=data), self.assertRaises(InvalidDiagram):
                read_diagram(data)

    def test_non_spherical_rotation_is_rejected(self):
        with self.assertRaisesRegex(InvalidDiagram, "sphere"):
            PlanarDiagram(((0, 1, 2, 3), (0, 1, 3, 2)))

    def test_label_normalization(self):
        d = braid_closure(3, [1, -2, 1, -2])
        relabelled = PlanarDiagram(tuple(tuple(20 * x - 30 for x in row) for row in d.crossings))
        self.assertEqual(d, relabelled)

    def test_sphere_euler(self):
        for m, word in ((2, [1] * 5), (3, [1, -2] * 2), (3, [1, 2] * 5)):
            d = braid_closure(m, word)
            self.assertEqual(len(d.face_darts()), d.n + 2)

    def test_mirror_involution(self):
        d = braid_closure(2, [1] * 3)
        # Two swaps are a 180-degree cyclic change, not literal tuple identity.
        self.assertEqual(knot_determinant(d), knot_determinant(d.mirror().mirror()))


class ReductionTests(unittest.TestCase):
    def test_curls(self):
        for word in ([1], [-1], [1, 2], [-1, -2]):
            d = braid_closure(max(map(abs, word)) + 1, word)
            reduced, trace = simplify(d)
            self.assertEqual(reduced.n, 0)
            self.assertEqual(verify_reduction_trace(d, [x.to_json() for x in trace]), reduced)

    def test_bigons(self):
        for word in ([1, -1, 1], [-1, 1, -1], [1, 2, -2, -1, 1, 2]):
            d = braid_closure(max(map(abs, word)) + 1, word)
            reduced, trace = simplify(d)
            self.assertEqual(reduced.n, 0)
            self.assertTrue(any(x.kind == 'R2' for x in trace))

    def test_clasp_is_not_r2(self):
        self.assertFalse(legal_reductions(braid_closure(2, [1, 1, 1])))

    def test_reject_forged_trace(self):
        d = braid_closure(2, [1, 1, 1])
        with self.assertRaises(ValueError):
            verify_reduction_trace(d, [{'kind': 'R2', 'vertices': [0, 1], 'face_darts': [0, 1]}])

    def test_hard_unknot_remains(self):
        d = braid_closure(3, [-2, -2, -2, 2, 1, 1, 2, 1])
        reduced, trace = simplify(d)
        self.assertEqual(reduced.n, 6)
        self.assertEqual(len(trace), 1)


class KhovanovTests(unittest.TestCase):
    def test_known_ranks_and_d_squared(self):
        cases = ((1, [], 1), (2, [1], 1), (2, [-1], 1),
                 (2, [1] * 3, 3), (2, [1] * 5, 5), (2, [1] * 7, 7),
                 (3, [1, -2] * 2, 5), (3, [1, 2] * 5, 7),
                 (3, [-2, -2, -2, 2, 1, 1, 2, 1], 1))
        for m, word, expected in cases:
            with self.subTest(strands=m, word=word):
                result = ReducedComplex(braid_closure(m, word)).compute(check_d_squared=True)
                self.assertEqual(result.total_rank, expected)
                self.assertEqual(sum((-1) ** k * d for k, d in enumerate(result.homology_dimensions)),
                                 sum((-1) ** k * d for k, d in enumerate(result.chain_dimensions)))

    def test_determinants(self):
        for m, word, expected in ((1, [], 1), (2, [1], 1), (2, [1] * 3, 3),
                                  (2, [1] * 5, 5), (3, [1, -2] * 2, 5),
                                  (3, [1, 2] * 5, 1)):
            self.assertEqual(knot_determinant(braid_closure(m, word)), expected)

    def test_nontrivial_determinant_one(self):
        d = braid_closure(3, [1, 2] * 5)
        result = recognize(d, check_d_squared=True)
        self.assertEqual(result['determinant'], 1)
        self.assertEqual(result['status'], 'NONTRIVIAL')
        self.assertEqual(result['khovanov']['total_rank'], 7)
        self.assertFalse(result['quasipolynomial_guarantee'])

    def test_positive_fallback_without_reductions(self):
        d = braid_closure(3, [-2, -2, -2, 2, 1, 1, 2, 1])
        result = recognize(d, reduce=False, determinant=False)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['khovanov']['total_rank'], 1)

    def test_mirror_ranks(self):
        for m, w in ((2, [1] * 3), (3, [1, -2] * 2), (3, [1, 2] * 4)):
            d = braid_closure(m, w)
            a = ReducedComplex(d).compute().homology_dimensions
            b = ReducedComplex(d.mirror()).compute().homology_dimensions
            self.assertEqual(a, tuple(reversed(b)))

    def test_basepoint_independence(self):
        d = braid_closure(3, [1, -2] * 2)
        ranks = [ReducedComplex(d, marked_edge=e).compute().total_rank for e in range(2 * d.n)]
        self.assertEqual(ranks, [5] * (2 * d.n))

    def test_reidemeister_iii_braid_relation(self):
        # sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2; tails close to one component.
        for tail in ([1], [-1], [2], [-2]):
            left = braid_closure(3, [1, 2, 1] + tail)
            right = braid_closure(3, [2, 1, 2] + tail)
            self.assertEqual(ReducedComplex(left).compute().total_rank,
                             ReducedComplex(right).compute().total_rank)

    def test_markov_stabilization(self):
        trefoil = braid_closure(2, [1] * 3)
        for last in (2, -2):
            stabilized = braid_closure(3, [1, 1, 1, last])
            self.assertEqual(ReducedComplex(stabilized).compute().total_rank,
                             ReducedComplex(trefoil).compute().total_rank)

    def test_resource_caps_are_unknown(self):
        d = braid_closure(3, [1, 2] * 5)
        for caps in ({'max_resolutions': 8}, {'max_basis': 5}):
            with self.assertRaises(ResourceLimit):
                ReducedComplex(d, **caps)
            result = recognize(d, **caps)
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertIsNone(result['is_unknot'])
        for cap in (0, -1, True):
            with self.assertRaises(ValueError):
                recognize(d, max_basis=cap)

    def test_random_reduction_invariance(self):
        rng = random.Random(998877)
        checked = 0
        while checked < 50:
            m = rng.choice((2, 3, 4))
            n = rng.randrange(1, 8)
            w = [rng.choice((-1, 1)) * rng.randrange(1, m) for _ in range(n)]
            try:
                d = braid_closure(m, w)
            except InvalidDiagram:
                continue
            smaller, trace = simplify(d)
            before = ReducedComplex(d).compute(check_d_squared=True)
            after = ReducedComplex(smaller).compute()
            self.assertEqual(before.total_rank, after.total_rank)
            self.assertEqual(knot_determinant(d), knot_determinant(smaller))
            self.assertEqual(verify_reduction_trace(d, [r.to_json() for r in trace]), smaller)
            checked += 1


if __name__ == '__main__':
    unittest.main()
