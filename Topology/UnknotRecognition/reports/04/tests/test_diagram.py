import json
import unittest

from unknot import Diagram, DiagramError, recognize


class DiagramTests(unittest.TestCase):
    def test_empty_means_one_circle(self):
        self.assertEqual(Diagram.from_pd([]).crossings, 0)
        self.assertEqual(recognize(Diagram.from_pd([])).status, 'UNKNOT')

    def test_normalizes_arbitrary_labels(self):
        old = Diagram.from_braid(2, [1, 1, 1])
        labels = {i: 2**128 + 107*i for i in range(old.edges)}
        new = Diagram.from_pd([[labels[x] for x in c] for c in old.pd], labels[0])
        self.assertEqual(old, new)

    def test_bad_arities(self):
        for value in [None, 3, 'PD', {}, [None], [[0, 0]], [[0]*5]]:
            with self.subTest(value=value), self.assertRaises(DiagramError):
                Diagram.from_pd(value)

    def test_bad_labels(self):
        for value in [[[True, 1, 1, True]], [[-1, 0, 0, -1]], [[0.0, 1, 1, 0.0]]]:
            with self.subTest(value=value), self.assertRaises(DiagramError):
                Diagram.from_pd(value)

    def test_bad_multiplicity(self):
        for value in [[[0, 0, 0, 0]], [[0, 1, 2, 3]], [[0, 1, 0, 2]]]:
            with self.subTest(value=value), self.assertRaises(DiagramError):
                Diagram.from_pd(value)

    def test_bad_mark(self):
        for pd, mark in [([], 1), ([], True), ([[0, 1, 1, 0]], 4),
                         ([[0, 1, 1, 0]], True)]:
            with self.subTest(mark=mark), self.assertRaises(DiagramError):
                Diagram.from_pd(pd, mark)

    def test_hopf_link_rejected(self):
        with self.assertRaisesRegex(DiagramError, '2 components'):
            Diagram.from_braid(2, [1, 1])

    def test_crossing_free_extra_strand_rejected(self):
        with self.assertRaisesRegex(DiagramError, 'components'):
            Diagram.from_braid(3, [1])

    def test_virtual_rotation_rejected(self):
        trefoil = Diagram.from_braid(2, [1]*3)
        rows = list(trefoil.pd)
        a, b, c, d = rows[0]
        rows[0] = (a, d, c, b)
        with self.assertRaisesRegex(DiagramError, 'nonplanar'):
            Diagram.from_pd(rows)

    def test_direct_constructor_cannot_bypass_validation(self):
        with self.assertRaises(DiagramError):
            recognize(Diagram(((0, 0, 0, 0),)))

    def test_braid_input_validation(self):
        for m, word in [(0, []), (True, []), (2, [0]), (2, [2]),
                        (2, [True]), (2, None), (2, '1'), (2, {})]:
            with self.subTest(m=m, word=word), self.assertRaises(DiagramError):
                Diagram.from_braid(m, word)

    def test_json_roundtrip(self):
        diagram = Diagram.from_braid(3, [1, -2]*2)
        self.assertEqual(diagram, Diagram.from_json(json.loads(json.dumps(diagram.to_json()))))

    def test_json_ambiguity_and_typos(self):
        for value in [{'pd': [], 'braid': {}}, {'pd': [], 'basepont': 3},
                      {'braid': {'strands': 2}}, {'braid': {}, 'unexpected': 1},
                      {'gauss': []}, None]:
            with self.subTest(value=value), self.assertRaises(DiagramError):
                Diagram.from_json(value)

    def test_mirror_is_involution_on_rank(self):
        d = Diagram.from_braid(3, [1, -2]*2)
        self.assertEqual(recognize(d).reduced_rank,
                         recognize(d.mirror().mirror()).reduced_rank)


if __name__ == '__main__':
    unittest.main()
