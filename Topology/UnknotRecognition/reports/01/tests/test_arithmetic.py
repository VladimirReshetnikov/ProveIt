import itertools
import random
import unittest
from unknot.determinant import bareiss, coloring_matrix, determinant
from unknot import Grid
from unknot.normal import from_cocycle
from unknot.potential import HierarchyPotential


def laplace(a):
    if not a:
        return 1
    return sum((-1) ** j * value * laplace([row[:j] + row[j + 1:] for row in a[1:]])
               for j, value in enumerate(a[0]))


class ArithmeticTests(unittest.TestCase):
    def test_bareiss_against_independent_expansion(self):
        rng = random.Random(77)
        for n in range(7):
            for _ in range(20):
                matrix = [[rng.randrange(-4, 5) for _ in range(n)] for _ in range(n)]
                self.assertEqual(bareiss(matrix), laplace(matrix))
        self.assertEqual(bareiss([[0, 1], [1, 0]]), -1)
        with self.assertRaises(ValueError):
            bareiss([[1, 2]])
        with self.assertRaises(ValueError):
            bareiss([[1.0]])

    def test_coloring_matrix(self):
        grid = Grid.from_json({"x": list(range(5)), "o": [2, 3, 4, 0, 1]})
        matrix = coloring_matrix(grid)
        self.assertEqual(len(matrix), 3)
        self.assertTrue(all(sum(row) == 0 for row in matrix))
        self.assertEqual(determinant(grid), 3)
        for r in range(3):
            for c in range(3):
                minor = [row[:c] + row[c + 1:] for i, row in enumerate(matrix) if i != r]
                self.assertEqual(abs(bareiss(minor)), 3)

    def test_normal_coordinates_and_matching(self):
        tetrahedra = [(0, 1, 2, 3), (2, 0, 1, 4)]
        heights = [0, 2, 5, 9, 6]
        edges = {tuple(sorted(e)) for t in tetrahedra for e in itertools.combinations(t, 2)}
        cocycle = {(a, b): heights[b] - heights[a] for a, b in edges}
        result = from_cocycle(tetrahedra, cocycle)
        self.assertTrue(result.check_matching())
        self.assertEqual(result.coordinates[0], (2, 0, 0, 4, 3, 0, 0))
        self.assertEqual(result.face_arcs(0, (0, 1, 2)), {0: 2, 1: 0, 2: 3})
        self.assertEqual(result.face_arcs(0, (0, 1, 2)),
                         result.face_arcs(1, (0, 1, 2)))

    def test_normal_coordinates_without_expansion(self):
        big = 10 ** 1000
        heights = [-3 * big, big, 5 * big, 8 * big]
        cocycle = {(a, b): heights[b] - heights[a] for a, b in itertools.combinations(range(4), 2)}
        result = from_cocycle([(0, 1, 2, 3)], cocycle)
        self.assertEqual(result.coordinates, ((4 * big, 0, 0, 3 * big, 4 * big, 0, 0),))
        self.assertEqual(len(result.coordinates[0]), 7)

    def test_normal_coordinates_against_sheet_enumeration(self):
        rng = random.Random(2026)
        pairs = ({0, 1}, {0, 2}, {0, 3})
        for _ in range(200):
            h = [rng.randrange(-10, 11) for _ in range(4)]
            cocycle = {(a, b): h[b] - h[a] for a, b in itertools.combinations(range(4), 2)}
            actual = from_cocycle([(0, 1, 2, 3)], cocycle).coordinates[0]
            expected = [0] * 7
            for k in range(min(h), max(h)):
                below = {i for i in range(4) if h[i] <= k}
                if len(below) in (1, 3):
                    isolated = below if len(below) == 1 else set(range(4)) - below
                    expected[next(iter(isolated))] += 1
                else:
                    split = below if 0 in below else set(range(4)) - below
                    expected[4 + pairs.index(split)] += 1
            self.assertEqual(actual, tuple(expected))
            self.assertLessEqual(sum(x > 0 for x in actual[4:]), 1)

    def test_normal_validation(self):
        for tets, cocycle in [([(0, 1, 2, 3)], {(0, 1): 1}),
                              ([(0, 1, 2, 3)], {(1, 0): 1}),
                              ([(0, 1, 2, 3)], {(0, 4): 1}),
                              ([(0, 0, 1, 2)], {}),
                              ([(0, 1, 2, 3), (3, 2, 1, 0)], {}),
                              ([(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 2, 5)], {})]:
            with self.subTest(tets=tets, cocycle=cocycle), self.assertRaises(ValueError):
                from_cocycle(tets, cocycle)

    def test_potential_all_suffix_resets(self):
        potential = HierarchyPotential(3, 4)
        self.assertEqual(potential.simplification_bound, 255)
        self.assertEqual(potential.loop_bound, 1024)
        self.assertEqual(potential.value((1,)), 64)
        for before in itertools.product(range(4), repeat=4):
            for j in range(4):
                if before[j]:
                    after = before[:j] + (before[j] - 1,) + (3,) * (3 - j)
                    self.assertTrue(potential.check_simplification(before, after, j))
        self.assertFalse(potential.check_simplification((1, 2), (1, 3), 1))
        self.assertFalse(potential.check_simplification((2, 2), (1, 1), 1))
        with self.assertRaises(ValueError):
            potential.value((4,))
        with self.assertRaises(ValueError):
            potential.value((1,) * 5)

    def test_base_g_would_not_suffice(self):
        potential = HierarchyPotential(3, 3)
        self.assertGreater(potential.value((1, 0, 0)), potential.value((0, 3, 3)))
        # In base g=3, the corresponding padded "digits" give 9 and 12: wrong order.
        self.assertLess(1 * 3 ** 2, 3 * 3 + 3)

class NonExactCocycleTests(unittest.TestCase):
    def test_product_solid_torus(self):
        from tools.solid_torus import example
        tets, cocycle = example()
        result = from_cocycle(tets, cocycle)
        self.assertTrue(result.check_matching())
        self.assertEqual(sum(sum(row) for row in result.coordinates), 3)
        # A loop along the first vertex of each triangle has cocycle period 1.
        self.assertEqual(cocycle.get((0, 3), 0) + cocycle.get((3, 6), 0)
                         - cocycle.get((0, 6), 0), 1)
        multiple = from_cocycle(tets, {e: 10 ** 500 * x for e, x in cocycle.items()})
        self.assertEqual(multiple.coordinates,
                         tuple(tuple(10 ** 500 * x for x in row) for row in result.coordinates))

class CohomologyTests(unittest.TestCase):
    def test_balls_have_zero_first_cohomology(self):
        from unknot.cohomology import rational_cohomology_basis
        self.assertEqual(rational_cohomology_basis([]), [])
        self.assertEqual(rational_cohomology_basis([(0, 1, 2, 3)]), [])
        self.assertEqual(rational_cohomology_basis([(0, 1, 2, 3), (0, 1, 2, 4)]), [])

    def test_solid_torus_basis_is_nonexact(self):
        from unknot.cohomology import rational_cohomology_basis
        from tools.solid_torus import example
        tetrahedra, _ = example()
        basis = rational_cohomology_basis(tetrahedra)
        self.assertEqual(len(basis), 1)
        c = basis[0]
        period = c.get((0, 3), 0) + c.get((3, 6), 0) - c.get((0, 6), 0)
        self.assertNotEqual(period, 0)
        result = from_cocycle(tetrahedra, c)
        self.assertTrue(result.check_matching())
        self.assertGreater(sum(sum(row) for row in result.coordinates), 0)

    def test_two_components_give_two_classes(self):
        from unknot.cohomology import rational_cohomology_basis
        from tools.solid_torus import example
        tetrahedra, _ = example()
        both = tetrahedra + [tuple(v + 9 for v in t) for t in tetrahedra]
        basis = rational_cohomology_basis(both)
        self.assertEqual(len(basis), 2)
        for c in basis:
            self.assertTrue(from_cocycle(both, c).check_matching())

    def test_cohomology_validation(self):
        from unknot.cohomology import rational_cohomology_basis
        for tets in [[(0, 0, 1, 2)], [(0, 1, 2)], [(0, 1, 2, 3), (3, 2, 1, 0)]]:
            with self.assertRaises(ValueError):
                rational_cohomology_basis(tets)
