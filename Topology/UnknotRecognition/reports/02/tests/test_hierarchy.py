from __future__ import annotations
from itertools import combinations, permutations, product
import random
import unittest
from unknotlab.normal import (Triangulation, SignedDSU, one_tetrahedron_ball,
                              one_tetrahedron_solid_torus)
from unknotlab.pattern import BallPattern
from unknotlab.potential import HierarchyBudget


class NormalSurfaceTests(unittest.TestCase):
    def test_ball_cohomology(self):
        t = one_tetrahedron_ball()
        self.assertEqual(t.edge_count, 6)
        self.assertEqual(t.rational_cohomology_basis(), [])
        self.assertEqual(sorted(v['chi'] for v in t.vertex_links.values()), [1, 1, 1, 1])

    def test_ball_exact_cocycle(self):
        t = one_tetrahedron_ball()
        heights = [0, 2, -3, 1]
        cocycle = [heights[b] - heights[a] for a, b in combinations(range(4), 2)]
        s = t.dual_surface(cocycle)
        self.assertEqual(s.disc_count, 5)
        self.assertEqual(s.euler_characteristic, 5)
        t.check_normal_coordinates(s.coordinates)

    def test_solid_torus_disc(self):
        t = one_tetrahedron_solid_torus()
        basis = t.rational_cohomology_basis()
        self.assertEqual(basis, [(3, -1, -2)])
        s = t.dual_surface(basis[0])
        self.assertEqual(s.coordinates, ((1, 1, 0, 0, 0, 0, 1),))
        self.assertEqual(s.euler_characteristic, 1)
        self.assertEqual(s.disc_count, 3)
        t.check_normal_coordinates(s.coordinates)

    def test_large_compressed_coordinates(self):
        t = one_tetrahedron_solid_torus()
        factor = 10 ** 1000
        s = t.dual_surface([3 * factor, -factor, -2 * factor])
        self.assertEqual(s.disc_count, 3 * factor)
        self.assertEqual(s.euler_characteristic, factor)
        self.assertLess(s.coordinate_bits, 10000)
        self.assertEqual(len(s.coordinates), 1)  # never expands the disks

    def test_orientation_reversal(self):
        t = one_tetrahedron_solid_torus()
        self.assertEqual(t.dual_surface([3, -1, -2]).coordinates,
                         t.dual_surface([-3, 1, 2]).coordinates)

    def test_zero_surface(self):
        t = one_tetrahedron_solid_torus()
        s = t.dual_surface([0] * t.edge_count)
        self.assertEqual(s.disc_count, 0)
        self.assertEqual(s.euler_characteristic, 0)

    def test_relabel_all_tetrahedron_vertices(self):
        t = one_tetrahedron_solid_torus()
        for q in permutations(range(4)):
            inverse = tuple(q.index(i) for i in range(4))
            glues = [None] * 4
            for f, gluing in enumerate(t.gluings[0]):
                if gluing is not None:
                    _, p = gluing
                    conjugate = tuple(q[p[inverse[v]]] for v in range(4))
                    glues[q[f]] = (0, conjugate)
            u = Triangulation([glues])
            basis = u.rational_cohomology_basis()
            self.assertEqual(len(basis), 1)
            s = u.dual_surface(basis[0])
            self.assertEqual(s.euler_characteristic, 1)
            self.assertEqual(s.disc_count, 3)

    def test_nonclosed_cochain(self):
        with self.assertRaisesRegex(ValueError, 'not closed'):
            one_tetrahedron_solid_torus().dual_surface([1, 0, 0])

    def test_normal_matching_and_quad_validation(self):
        t = one_tetrahedron_solid_torus()
        for rows in [((1, 0, 0, 0, 0, 0, 0),), ((0, 0, 0, 0, 1, 1, 0),),
                     ((-1, 0, 0, 0, 0, 0, 0),), ((0, 0, 0),)]:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                t.check_normal_coordinates(rows)

    def test_bad_gluing(self):
        cases = [[], [[None] * 3], [[(1, (1, 0, 2, 3)), None, None, None]],
                 [[(0, (1, 0, 2, 3)), None, None, None]],
                 [[(0, (0, 1, 2, 3)), None, None, None]],
                 [[(0, (1, 0, 3, 2)), (0, (1, 0, 3, 2)), None, None]]]
        for glues in cases:
            with self.subTest(glues=glues), self.assertRaises(ValueError):
                Triangulation(glues)

    def test_signed_union_find(self):
        d = SignedDSU(5)
        d.union(0, 1, -1)
        d.union(1, 2, -1)
        d.union(2, 3, 1)
        for a, b, sign in [(0, 1, -1), (0, 2, 1), (0, 3, 1), (1, 3, -1)]:
            ra, sa = d.find(a)
            rb, sb = d.find(b)
            self.assertEqual(ra, rb)
            self.assertEqual(sa * sb, sign)
        with self.assertRaises(ValueError):
            d.union(0, 2, -1)

    def test_two_tetrahedron_ball(self):
        t = Triangulation([[(1, (0, 2, 1, 3)), None, None, None],
                           [(0, (0, 2, 1, 3)), None, None, None]])
        self.assertEqual(t.rational_cohomology_basis(), [])
        self.assertEqual(len(t.vertex_links), 5)
        self.assertTrue(all(v['chi'] == 1 for v in t.vertex_links.values()))


def perfect_matchings(items):
    if not items:
        yield []
        return
    a = items[0]
    for i in range(1, len(items)):
        for rest in perfect_matchings(items[1:i] + items[i + 1:]):
            yield [(a, items[i])] + rest


def independent_essential_predicate(pattern):
    """Independent characterization via simple 4-connected dual (or K3/K4)."""
    if pattern.graph_components + pattern.circles <= 1 and not pattern.vertices:
        return True
    if pattern.graph_components + pattern.circles != 1:
        return False
    n = len(pattern.faces)
    adjacency = [set() for _ in range(n)]
    for a, b in pattern.edge_pairs:
        u, v = pattern.face_of[a], pattern.face_of[b]
        if u == v or v in adjacency[u]:
            return False
        adjacency[u].add(v)
        adjacency[v].add(u)
    if n in (3, 4):
        return all(len(row) == n - 1 for row in adjacency)
    if n < 5:
        return False
    for size in range(4):
        for removed in combinations(range(n), size):
            available = set(range(n)) - set(removed)
            found, stack = {min(available)}, [min(available)]
            while stack:
                u = stack.pop()
                for v in adjacency[u] & available - found:
                    found.add(v)
                    stack.append(v)
            if found != available:
                return False
    return True


class BoundaryPatternTests(unittest.TestCase):
    def test_empty_and_circle(self):
        self.assertTrue(BallPattern(0, []).test_essential().essential)
        self.assertTrue(BallPattern(0, [], circles=1).test_essential().essential)
        self.assertFalse(BallPattern(0, [], circles=2).test_essential().essential)

    def test_theta(self):
        p = BallPattern.from_dual_triangles([(0, 1, 2), (0, 2, 1)])
        self.assertTrue(p.test_essential().essential)
        q = BallPattern(p.vertices, list(p.edge_pairs), circles=1)
        self.assertFalse(q.test_essential().essential)

    def test_tetrahedral(self):
        p = BallPattern.from_dual_triangles([(0, 2, 1), (0, 1, 3), (0, 3, 2), (1, 2, 3)])
        self.assertTrue(p.test_essential().essential)

    def test_bipyramids(self):
        for size in range(3, 9):
            vertices = list(range(2, size + 2))
            faces = []
            for i, j in zip(vertices, vertices[1:] + vertices[:1]):
                faces.extend([(0, i, j), (1, j, i)])
            p = BallPattern.from_dual_triangles(faces)
            result = p.test_essential()
            self.assertEqual(result.essential, size > 3)
            self.assertEqual(result.essential, independent_essential_predicate(p))
            if size == 3:
                self.assertEqual(len(result.dual_cycle), 3)
                self.assertEqual(len(result.crossed_edges), 3)

    def test_loop_obstruction(self):
        p = BallPattern(2, [(0, 1), (2, 3), (4, 5)])
        result = p.test_essential()
        self.assertFalse(result.essential)
        self.assertEqual(len(result.dual_cycle), 1)

    def test_all_matchings_four_vertices(self):
        count, parallel_obstructions = 0, 0
        for pairs in perfect_matchings(list(range(12))):
            try:
                p = BallPattern(4, pairs)
            except ValueError:  # non-spherical embedding
                continue
            count += 1
            result = p.test_essential()
            parallel_obstructions += len(result.dual_cycle) == 2
            self.assertEqual(result.essential, independent_essential_predicate(p))
        self.assertGreater(count, 100)
        self.assertGreater(parallel_obstructions, 0)

    def test_random_larger_rotation_systems(self):
        rng = random.Random(9917)
        count = 0
        for vertices in (6, 8, 10):
            for _ in range(1500):
                darts = list(range(3 * vertices))
                rng.shuffle(darts)
                try:
                    p = BallPattern(vertices, list(zip(darts[::2], darts[1::2])))
                except ValueError:
                    continue
                count += 1
                self.assertEqual(p.test_essential().essential, independent_essential_predicate(p))
        self.assertGreater(count, 50)

    def test_bad_pattern(self):
        for args in [(True, []), (1, []), (2, [(0, 1), (2, 3), (4, 4)])]:
            with self.assertRaises(ValueError):
                BallPattern(*args)
        with self.assertRaises(ValueError):
            BallPattern.from_dual_triangles([(0, 1, 2)])


class PotentialTests(unittest.TestCase):
    def test_exact_base(self):
        b = HierarchyBudget(2, 2)
        self.assertEqual(b.value([1, 0]), 3)
        self.assertEqual(b.value([0, 2]), 2)
        self.assertEqual(b.verify_replacement([1, 0], [0, 2], 0), 1)

    def test_padding_and_maximum(self):
        b = HierarchyBudget(3, 5)
        self.assertEqual(b.value([1]), 256)
        self.assertEqual(b.max_value, 1023)
        self.assertEqual(b.value([3] * 5), b.max_value)

    def test_exhaustive_order(self):
        b = HierarchyBudget(3, 4)
        digits = list(product(range(4), repeat=4))
        self.assertEqual([b.value(d) for d in digits], list(range(256)))
        for before, after in zip(digits[1:], digits[:-1]):
            index = next(i for i in range(4) if before[i] != after[i])
            self.assertEqual(b.verify_replacement(before, after, index), 1)

    def test_reject_false_decrease(self):
        b = HierarchyBudget(2, 2)
        for a, c, i in [([1, 1], [1, 1], 0), ([1, 0], [0, 1], 1),
                        ([1, 0], [1, 2], 1), ([1, 0], [0, 4], 0)]:
            with self.assertRaises(ValueError):
                b.verify_replacement(a, c, i)

    def test_budget_is_only_conditional(self):
        b = HierarchyBudget(5, 3)
        self.assertEqual(b.conditional_operation_bound(restarts=7, work_per_step=11),
                         7 * 11 * 4 * 6 ** 3)
        self.assertEqual(HierarchyBudget(0, 0).max_value, 0)
        with self.assertRaises(ValueError):
            HierarchyBudget(-1, 3)
