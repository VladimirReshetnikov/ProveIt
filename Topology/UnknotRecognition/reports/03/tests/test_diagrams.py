import unittest

from unknot_lab.diagrams import InvalidDiagram, PlanarDiagram

TREFOIL = [[1, 4, 2, 5], [3, 6, 4, 1], [5, 2, 6, 3]]


class DiagramTests(unittest.TestCase):
    def test_trefoil(self):
        pd = PlanarDiagram.from_pd(TREFOIL)
        self.assertEqual(pd.n, 3)
        self.assertEqual(pd.faces, 5)
        self.assertEqual(pd.to_pd(), TREFOIL)

    def test_empty(self):
        self.assertEqual(PlanarDiagram.from_pd([]).n, 0)
        self.assertEqual(PlanarDiagram.from_braid(1, []).n, 0)

    def test_invalid_data(self):
        for bad in (None, {}, [[1, 2, 3]], [[1, 2, 3, 4]],
                    [[True, True, 2, 2]], [[1.0, 1.0, 2, 2]]):
            with self.subTest(bad=bad), self.assertRaises(InvalidDiagram):
                PlanarDiagram.from_pd(bad)

    def test_virtual_projection_rejected(self):
        with self.assertRaisesRegex(InvalidDiagram, "sphere"):
            PlanarDiagram.from_pd([[1, 2, 1, 2]])

    def test_disconnected_projection_rejected(self):
        with self.assertRaisesRegex(InvalidDiagram, "Disconnected"):
            PlanarDiagram.from_pd([[1, 1, 2, 2], [3, 3, 4, 4]])

    def test_link_closures_rejected(self):
        for strands, word in [(2, []), (2, [1, 1]), (3, [1]), (3, [1, -1])]:
            with self.subTest(word=word), self.assertRaises(InvalidDiagram):
                PlanarDiagram.from_braid(strands, word)

    def test_bad_braids(self):
        for strands, word in [(0, []), (True, []), (2, [0]), (2, [2]), (2, [True])]:
            with self.subTest(word=word), self.assertRaises(InvalidDiagram):
                PlanarDiagram.from_braid(strands, word)

    def test_json_ambiguity(self):
        for bad in [{}, {"pd": [], "braid": {}}, {"braid": {}}, {"braid": []}]:
            with self.subTest(bad=bad), self.assertRaises(InvalidDiagram):
                PlanarDiagram.from_json(bad)

    def test_braid_permutation_components(self):
        for strands in range(2, 6):
            word = list(range(1, strands))
            pd = PlanarDiagram.from_braid(strands, word)
            self.assertEqual(pd.n, strands - 1)
            self.assertEqual(pd.faces, strands + 1)

    def test_invalid_basepoint(self):
        with self.assertRaises(InvalidDiagram):
            PlanarDiagram.from_pd(TREFOIL).basepoint(100)

    def test_huge_invalid_braid_rejected_before_allocation(self):
        with self.assertRaises(InvalidDiagram):
            PlanarDiagram.from_braid(10 ** 100, [1])


if __name__ == "__main__":
    unittest.main()
