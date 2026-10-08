"""Independent finite optimization oracles and geometric seed audits."""

from copy import deepcopy
from dataclasses import replace
import importlib.util
from itertools import product, permutations
import random
import unittest

from fastunknot.cocycle_seed import (
    check_glued_normal_coordinates, check_seed_certificate, face_pairing_data,
    local_normal_coordinates, minimize_disc_seed, optimize_face_pairing_cocycle,
    optimize_triangulated_cocycle, verify_seed_certificate,
)
from benchmark_cocycle_seed import (
    load_archive_triangulation, product_solid_torus, regina_surface_summary,
    regina_triangulation, regina_gluings,
)


class CocycleSeedTests(unittest.TestCase):
    def test_local_coordinates_all_orders_ties_and_large_gaps(self):
        for heights in permutations((0, 1, 4, 11)):
            row = local_normal_coordinates(heights)
            self.assertEqual(sum(row), 11)
            self.assertEqual(sum(bool(value) for value in row[4:]), 1)
        self.assertEqual(local_normal_coordinates((3, 3, 3, 3)), (0,) * 7)
        large = 1 << 4096
        self.assertEqual(sum(local_normal_coordinates((0, large, large, 2 * large))),
                         2 * large)

    def test_exhaustive_potential_oracle(self):
        # Optimization is valid even for this abstract local incidence input;
        # no assertion that these random rows form a manifold is made.
        rng = random.Random(123456)
        for _ in range(120):
            count = rng.randrange(1, 6)
            vertices = tuple(tuple(rng.randrange(3) for _ in range(4))
                             for _ in range(count))
            heights = tuple(tuple(rng.randrange(-3, 4) for _ in range(4))
                            for _ in range(count))
            result = minimize_disc_seed(vertices, heights)
            labels = sorted({v for row in vertices for v in row})
            # For these three-vertex inputs a fixed zero potential and range
            # [-12,12] includes an optimal difference-constraint vertex.
            best = min(sum(max(h + f[v] for v, h in zip(vs, hs))
                           - min(h + f[v] for v, h in zip(vs, hs))
                           for vs, hs in zip(vertices, heights))
                       for tail in product(range(-12, 13), repeat=len(labels) - 1)
                       for f in [dict(zip(labels, (0,) + tail))])
            self.assertEqual(result.disc_count, best)
            self.assertTrue(verify_seed_certificate(vertices, heights, result))

    def test_exhaustive_dual_permutation_oracle(self):
        rng = random.Random(161803)
        for _ in range(25):
            n = 5
            vertices = tuple(tuple(rng.randrange(4) for _ in range(4)) for _ in range(n))
            heights = tuple(tuple(rng.randrange(-50, 51) for _ in range(4)) for _ in range(n))
            costs = {}
            for t in range(n):
                for s in range(n):
                    allowed = [heights[s][j] - heights[t][i]
                               for i in range(4) for j in range(4)
                               if vertices[t][i] == vertices[s][j]]
                    if allowed:
                        costs[t, s] = max(allowed)
            best = max(sum(costs[t, s] for t, s in enumerate(p))
                       for p in permutations(range(n))
                       if all((t, s) in costs for t, s in enumerate(p)))
            self.assertEqual(minimize_disc_seed(vertices, heights).disc_count, best)

    def test_binary_height_scaling_does_not_expand_network(self):
        gluings, h = product_solid_torus(3, 1 << 16)
        _, vertices, h = face_pairing_data(gluings, h)
        small = minimize_disc_seed(vertices, h)
        gluings, h = product_solid_torus(3, 1 << 4096)
        _, vertices, h = face_pairing_data(gluings, h)
        large = minimize_disc_seed(vertices, h)
        self.assertEqual(large.disc_count, 3)
        self.assertEqual(large.statistics['augmentations'], 9)
        self.assertEqual(large.statistics['network_arcs'], small.statistics['network_arcs'])
        self.assertEqual(large.statistics['network_nodes'], small.statistics['network_nodes'])
        self.assertGreater(large.initial_disc_count.bit_length(), 4096)

    def test_one_vertex_gauge_is_vacuous(self):
        vertices = ((4, 4, 4, 4), (4, 4, 4, 4))
        heights = ((-7, 1, 2, 9), (0, 2, 1, 1 << 4096))
        result = minimize_disc_seed(vertices, heights)
        self.assertEqual(result.disc_count, result.initial_disc_count)
        self.assertEqual(result.potential, (0,))

    def test_exact_class_can_disappear(self):
        result = minimize_disc_seed(((0, 1, 2, 3),), ((3, -11, 9, 42),))
        self.assertEqual(result.disc_count, 0)
        self.assertEqual(result.normal_coordinates, ((0,) * 7,))

    def test_disconnected_incidence_system(self):
        result = minimize_disc_seed(((0, 1, 1, 0), (5, 6, 6, 5)),
                                    ((0, 3, 4, 2), (-2, 8, 5, 7)))
        self.assertTrue(verify_seed_certificate(((0, 1, 1, 0), (5, 6, 6, 5)),
                                               ((0, 3, 4, 2), (-2, 8, 5, 7)), result))

    def test_independent_certificate_rejects_corruption(self):
        gluings, heights = product_solid_torus(3, 123)
        _, vertices, heights = face_pairing_data(gluings, heights)
        result = minimize_disc_seed(vertices, heights)
        data = result.as_dict()
        for key in ('initial_disc_count', 'disc_count'):
            bad = deepcopy(data)
            bad[key] += 1
            self.assertFalse(verify_seed_certificate(vertices, heights, bad))
        bad = deepcopy(data)
        bad['normal_coordinates'][0][0] += 1
        self.assertFalse(verify_seed_certificate(vertices, heights, bad))
        bad = deepcopy(data)
        bad['matching'][0] = bad['matching'][1]
        self.assertFalse(verify_seed_certificate(vertices, heights, bad))
        bad = deepcopy(data)
        bad['potential'][0] = float(bad['potential'][0])
        self.assertFalse(verify_seed_certificate(vertices, heights, bad))
        bad = deepcopy(data)
        bad['vertex_ids'].reverse()
        self.assertFalse(verify_seed_certificate(vertices, heights, bad))

    def test_potential_global_shift_preserves_certificate(self):
        vertices, heights = ((0, 1, 2, 0),), ((0, -1, 2, 3),)
        result = minimize_disc_seed(vertices, heights)
        shifted = replace(result, potential=tuple(v + 10**80 for v in result.potential))
        self.assertTrue(verify_seed_certificate(vertices, heights, shifted))

    def test_cancel_callback(self):
        class Cancelled(Exception):
            pass
        def cancel():
            raise Cancelled
        with self.assertRaises(Cancelled):
            minimize_disc_seed(((0, 1, 2, 3),), ((0, 1, 2, 3),), cancel)

    def test_product_torus_normal_matching_and_primitive_disk(self):
        for steps in (3, 4, 7):
            gluings, heights = product_solid_torus(steps, 13579)
            result = optimize_face_pairing_cocycle(gluings, heights)
            self.assertEqual(result.disc_count, 3)
            self.assertTrue(check_glued_normal_coordinates(gluings, result.normal_coordinates))
            self.assertGreater(result.initial_disc_count, result.disc_count)

    def test_gluing_adapter_rejects_bad_input(self):
        gluings, heights = product_solid_torus()
        changed = [list(row) for row in heights]
        changed[0][0] += 1
        with self.assertRaises(ValueError):
            face_pairing_data(gluings, changed)
        with self.assertRaises(ValueError):
            face_pairing_data([[(0, (0, 1, 2, 3)), None, None, None]], [(0, 0, 0, 0)])
        for vertices, local in (([], []), (((0, 1, 2, True),), ((0, 1, 2, 3),)),
                                 (((0, 1, 2, 3),), ((0, 1, 2, 3.0),))):
            with self.assertRaises(ValueError):
                minimize_disc_seed(vertices, local)

    def test_archive02_finite_manifold_and_adapter(self):
        Triangulation = load_archive_triangulation()
        if Triangulation is None:
            self.skipTest('archive02 finite triangulation validator not present')
        gluings, heights = product_solid_torus(4, 0)
        tri = Triangulation(gluings)
        self.assertTrue(all(link['chi'] == 1 for link in tri.vertex_links.values()))
        basis = tri.rational_cohomology_basis()
        self.assertEqual(len(basis), 1)
        result, surface = optimize_triangulated_cocycle(tri, basis[0])
        self.assertEqual(result.disc_count, 3)
        self.assertEqual(surface.euler_characteristic, 1)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina unavailable')
    def test_regina_independent_manifold_and_connectedness(self):
        import regina
        gluings, heights = product_solid_torus(5, 1 << 80)
        result = optimize_face_pairing_cocycle(gluings, heights)
        tri = regina_triangulation(regina, gluings)
        info = regina_surface_summary(regina, tri, result.normal_coordinates)
        self.assertTrue(info['manifold_valid'])
        self.assertTrue(info['manifold_orientable'])
        self.assertFalse(info['manifold_ideal'])
        self.assertEqual(info['homology'], 'Z')
        self.assertTrue(info['surface_connected'])
        self.assertTrue(info['surface_orientable'])
        self.assertEqual(info['surface_euler_characteristic'], '1')
        self.assertTrue(info['surface_has_real_boundary'])
        self.assertEqual(info['surface_boundary_components'], 1)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina unavailable')
    def test_regina_finite_knot_exterior_seeds(self):
        import regina
        Triangulation = load_archive_triangulation()
        if Triangulation is None:
            self.skipTest('archive02 finite triangulation validator not present')
        regina.RandomEngine.reseedWithDefault()
        for tri in (regina.ExampleLink.trefoil().complement(), regina.Example3.figureEight()):
            tri.idealToFinite()
            validated = Triangulation(regina_gluings(tri))
            basis = validated.rational_cohomology_basis()
            self.assertEqual(len(basis), 1)
            result, surface = optimize_triangulated_cocycle(validated, basis[0])
            self.assertLess(result.disc_count, result.initial_disc_count)
            info = regina_surface_summary(regina, tri, surface.coordinates)
            self.assertTrue(info['surface_connected'])
            self.assertTrue(info['surface_orientable'])
            self.assertEqual(info['surface_euler_characteristic'], '-1')
            self.assertEqual(info['surface_boundary_components'], 1)


if __name__ == '__main__':
    unittest.main()
