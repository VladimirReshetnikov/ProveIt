"""Binary normal surfaces: genuine manifolds, topology and independent oracles."""
from copy import deepcopy
import importlib.util
from itertools import combinations, permutations
import random
import unittest

from fastunknot.normal_surface_orbits import (
    NormalOrbitError, _prepare, normal_arc_pairings, normal_surface_topology,
)
from normal_orbit_research.fixtures import (
    export_surface, export_triangulation, layered_torus, regina_surface,
    regina_triangulation,
)


def literal_orbits(size, pairings):
    parents = list(range(size))
    def find(v):
        while parents[v] != v:
            parents[v] = parents[parents[v]]
            v = parents[v]
        return v
    for p in pairings:
        for k in range(p.b - p.a + 1):
            x, y = p.a + k, p.d - k if p.reverse else p.c + k
            parents[find(x)] = find(y)
    return len({find(v) for v in range(size)})


def relabel(triangulation, coordinates, rng):
    size = len(coordinates)
    order = list(range(size))
    rng.shuffle(order)
    maps = [rng.sample(range(4), 4) for _ in range(size)]
    faces, result = [[None] * 4 for _ in range(size)], [[0] * 7 for _ in range(size)]
    for t, row in enumerate(triangulation['tetrahedra']):
        mapping = maps[t]
        for f, record in enumerate(row):
            if record is not None:
                u, p = record['tetrahedron'], record['permutation']
                q = [0] * 4
                for v in range(4):
                    q[mapping[v]] = maps[u][p[v]]
                faces[order[t]][mapping[f]] = dict(tetrahedron=order[u], permutation=q)
        for v in range(4):
            result[order[t]][mapping[v]] = coordinates[t][v]
        for q in range(3):
            pair = {mapping[0], mapping[q + 1]}
            if 0 not in pair:
                pair = set(range(4)) - pair
            result[order[t]][4 + next(v for v in pair if v) - 1] = coordinates[t][4 + q]
    return {'tetrahedra': faces}, result


class NormalSurfaceOrbitTests(unittest.TestCase):
    def test_layered_meridians_and_literal_arc_graph(self):
        for count in range(1, 13):
            tri, coords = layered_torus(count)
            result = normal_surface_topology(tri, coords)
            self.assertEqual((result['components'], result['boundary_components'],
                              result['orientable_components'], result['genus']), (1, 1, 1, 0))
            self.assertTrue(result['compressing_disk'])
            for boundary in (False, True):
                size, pairings = normal_arc_pairings(tri, coords, boundary=boundary)
                self.assertEqual(literal_orbits(size, pairings), 1)

    def test_exponential_meridian_has_polynomial_description(self):
        tri, coords = layered_torus(128)
        result = normal_surface_topology(tri, coords)
        self.assertGreater(result['normal_disks'], 10 ** 26)
        self.assertEqual(result['components'], 1)
        self.assertTrue(result['compressing_disk'])
        self.assertLessEqual(result['queries']['surface']['pairings'], 6 * 128 + 6)

    def test_empty_and_huge_parallel_disks(self):
        tri, coords = layered_torus(3)
        for scale in (0, 1, 2, 7, 2 ** 500):
            scaled = [[hex(scale * value) for value in row] for row in coords]
            result = normal_surface_topology(tri, scaled)
            self.assertEqual(result['components'], scale)
            self.assertEqual(result['orientable_components'], scale)
            self.assertEqual(result['nonorientable_components'], 0)
            self.assertEqual(result['boundary_components'], scale)
            self.assertEqual(result['euler_characteristic'], scale)
            self.assertEqual(result['compressing_disk'], scale == 1)

    def test_vertex_link_disk_is_not_compressing(self):
        tri, _ = layered_torus(1)
        result = normal_surface_topology(tri, [[1, 1, 1, 1, 0, 0, 0]])
        self.assertEqual(result['components'], 1)
        self.assertEqual(result['euler_characteristic'], 1)
        self.assertFalse(result['compressing_disk'])

    def test_one_sided_multiples_and_orientation_double(self):
        tri, _ = layered_torus(1)
        for scale in (1, 2, 3, 8, 2 ** 501 + 1):
            result = normal_surface_topology(tri, [[0, 0, 0, 0, 0, scale, 0]])
            self.assertEqual(result['components'], (scale + 1) // 2)
            self.assertEqual(result['orientable_components'], scale // 2)
            self.assertEqual(result['nonorientable_components'], scale & 1)
            self.assertEqual(result['boundary_components'], scale)
            self.assertEqual(result['euler_characteristic'], 0)

    def test_relabelled_one_vertex_edge_orientations(self):
        rng = random.Random(261008119)
        tri, coords = layered_torus(7)
        for _ in range(36):
            changed, vector = relabel(tri, coords, rng)
            result = normal_surface_topology(changed, vector)
            self.assertTrue(result['compressing_disk'])
            self.assertEqual(result['components'], 1)

    def test_malformed_normal_vectors_and_manifolds(self):
        tri, coords = layered_torus(1)
        for bad in ([[1, 1, 0, 0, 0, 0, True]], [[1, 1, 0, 0, 0, 0, 1.0]],
                    [[1, 1, 0, 0, 0, 0, -1]], [[2, 1, 0, 0, 0, 0, 1]],
                    [[1, 1, 0, 0, 1, 0, 1]], [[1] * 6]):
            with self.assertRaises(NormalOrbitError):
                normal_surface_topology(tri, bad)
        for broken in ({}, {'tetrahedra': [[None] * 4]}):
            with self.assertRaises(NormalOrbitError):
                normal_surface_topology(broken, coords)
        broken = deepcopy(tri)
        broken['tetrahedra'][0][1] = None
        with self.assertRaises(NormalOrbitError):
            normal_surface_topology(broken, coords)

    def test_shared_cycle_budget_and_global_cancellation(self):
        tri, coords = layered_torus(5)
        full = normal_surface_topology(tri, coords)
        for budget in (0, 1, full['cycles'] - 1):
            result = normal_surface_topology(tri, coords, max_cycles=budget)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('compressing_disk', result)
            self.assertLessEqual(result['cycles'], budget)
        self.assertTrue(normal_surface_topology(tri, coords,
                                                max_cycles=full['cycles'])['compressing_disk'])
        class Cancelled(Exception):
            pass
        calls = 0
        def check():
            nonlocal calls
            calls += 1
            if calls == 150:
                raise Cancelled()
        with self.assertRaises(Cancelled):
            normal_surface_topology(tri, coords, check=check)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_native_surfaces_sums_and_all_component_types(self):
        import regina
        rng = random.Random(261008120)
        comparisons = 0
        for size in range(1, 7):
            raw, _ = layered_torus(size)
            tri = regina_triangulation(raw)
            surfaces = list(regina.NormalSurfaces(tri, regina.NS_STANDARD))
            vectors = [export_surface(s) for s in surfaces]
            for _ in range(20):
                left, right = rng.choice(vectors), rng.choice(vectors)
                if any(sum(bool(a or b) for a, b in zip(x[4:], y[4:])) > 1
                       for x, y in zip(left, right)):
                    continue
                a, b = rng.randrange(1, 4), rng.randrange(1, 4)
                vectors.append([[a * x + b * y for x, y in zip(l, r)]
                                for l, r in zip(left, right)])
            for vector in vectors:
                native = regina_surface(tri, vector)
                parts = native.components()
                result = normal_surface_topology(raw, vector)
                self.assertEqual(result['components'], len(parts))
                self.assertEqual(result['orientable_components'], sum(s.isOrientable() for s in parts))
                self.assertEqual(result['boundary_components'], native.countBoundaries())
                self.assertEqual(result['euler_characteristic'], int(str(native.eulerChar())))
                self.assertEqual(result['compressing_disk'], native.isCompressingDisc())
                comparisons += 1
        self.assertGreater(comparisons, 50)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina oracle absent')
    def test_all_one_face_pairing_manifold_validation(self):
        for f, g in combinations(range(4), 2):
            for p in permutations(range(4)):
                if p[f] != g:
                    continue
                faces = [None] * 4
                faces[f] = dict(tetrahedron=0, permutation=list(p))
                faces[g] = dict(tetrahedron=0, permutation=[p.index(v) for v in range(4)])
                raw = {'tetrahedra': [faces]}
                native = regina_triangulation(raw)
                expected = (native.isValid() and not native.isIdeal() and native.isOrientable()
                            and native.isConnected() and native.countBoundaryComponents() == 1
                            and native.boundaryComponent(0).eulerChar() == 0)
                try:
                    _prepare(raw, lambda: None)
                    actual = True
                except NormalOrbitError:
                    actual = False
                self.assertEqual(actual, expected)


if __name__ == '__main__':
    unittest.main()
