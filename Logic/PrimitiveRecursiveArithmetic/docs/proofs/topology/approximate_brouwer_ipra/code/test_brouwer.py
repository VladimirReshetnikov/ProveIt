"""Regression and exhaustive small-grid checks. Run python code/test_brouwer.py."""

from collections import Counter
from fractions import Fraction as Q
from itertools import product
import unittest

from brouwer import (
    Cell, barycentric, cell_vertices, cells, check_witness, example_map,
    find_witness, grid, label, rational_point, sample_grid,
)


from cube import (
    check_cube_witness, disk_example, disk_map_on_square, find_cube_witness,
    retract_ball, sample_cube,
)


from named_simplex import check_named_tail, find_named_witness, staged_rotation


class FiniteBrouwerTests(unittest.TestCase):
    def test_mesh_incidence_and_diameter(self):
        for d, n in ((1, 1), (1, 9), (2, 2), (2, 5), (3, 3), (4, 3)):
            with self.subTest(d=d, n=n):
                simplices = list(cells(d, n))
                self.assertEqual(len(simplices), n ** d)
                self.assertEqual(len(set(simplices)), n ** d)
                faces = Counter()
                for cell in simplices:
                    vertices = tuple(cell_vertices(cell))
                    points = [barycentric(u, n) for u in vertices]
                    for coordinates in zip(*points):
                        self.assertLessEqual(max(coordinates) - min(coordinates), Q(1, n))
                    for j in range(d + 1):
                        faces[vertices[:j] + vertices[j + 1:]] += 1
                for face, incidence in faces.items():
                    face_points = [barycentric(u, n) for u in face]
                    boundary = any(all(t == 0 for t in column) for column in zip(*face_points))
                    self.assertEqual(incidence, 1 if boundary else 2)

    def test_all_support_labelings(self):
        for d, n, expected in ((0, 7, 1), (1, 4, 8), (2, 2, 8),
                               (2, 3, 192), (3, 2, 64)):
            with self.subTest(d=d, n=n):
                vertices = list(grid(d, n))
                supports = [
                    tuple(i for i, x in enumerate(barycentric(u, n)) if x > 0)
                    for u in vertices
                ]
                index = {u: k for k, u in enumerate(vertices)}
                simplex_ids = [tuple(index[u] for u in cell_vertices(c)) for c in cells(d, n)]
                checked = 0
                for coloring in product(*supports):
                    rainbow_count = sum(
                        len({coloring[k] for k in simplex}) == d + 1 for simplex in simplex_ids
                    )
                    self.assertEqual(rainbow_count % 2, 1)
                    checked += 1
                self.assertEqual(checked, expected)

    def test_example_maps(self):
        for d, n in ((0, 1), (0, 5), (1, 13), (2, 5), (3, 5), (4, 3)):
            for name in ("identity", "rotate", "constant", "quadratic"):
                with self.subTest(d=d, n=n, name=name):
                    samples = sample_grid(d, n, lambda x: example_map(name, x))
                    cell = find_witness(d, n, samples)
                    result = check_witness(d, n, samples, cell)
                    self.assertLessEqual(result["sample_residual_sup"], result["sample_residual_bound"])
                    for u, q in samples.items():
                        x = barycentric(u, n)
                        i = label(x, q)
                        self.assertGreater(x[i], 0)
                        self.assertEqual(x[i] - q[i], max(t - s for t, s in zip(x, q)))
                    if name == "identity":
                        self.assertEqual(result["sample_residual_sup"], 0)
                    if name in ("identity", "rotate"):
                        self.assertLessEqual(result["sample_oscillation_on_cell"], Q(1, n))

    def test_worked_rotation(self):
        samples = sample_grid(2, 5, lambda x: example_map("rotate", x))
        cell = find_witness(2, 5, samples)
        self.assertEqual(cell, Cell((1, 3), (0, 1)))
        result = check_witness(2, 5, samples, cell)
        self.assertEqual(result["vertex_labels"], [2, 0, 1])
        self.assertEqual(result["sample_residual_sup"], Q(1, 5))
        self.assertEqual(result["sample_residual_bound"], Q(8, 15))

    def test_cube_examples(self):
        for d, n in ((0, 3), (1, 11), (2, 5), (3, 3)):
            for f in (lambda x: x, lambda x: tuple(1 - t for t in x),
                      lambda x: (Q(1, 3),) * len(x)):
                samples = sample_cube(d, n, f)
                cell = find_cube_witness(d, n, samples)
                result = check_cube_witness(d, n, samples, cell)
                self.assertLessEqual(result["sample_residual_sup"], result["sample_residual_bound"])
                self.assertLessEqual(result["sample_oscillation_on_cell"], Q(1, n))
        samples = sample_cube(2, 5, lambda x: (1 - x[1], x[0]))
        result = check_cube_witness(2, 5, samples, find_cube_witness(2, 5, samples))
        self.assertEqual(result["anchor"], (Q(2, 5), Q(2, 5)))
        self.assertEqual(result["vertex_labels"], [0, 1, 2])
        self.assertEqual(result["sample_residual_sup"], Q(1, 5))

    def test_ball_retraction_and_disk(self):
        def sqdist(z, w):
            return sum((a - b) ** 2 for a, b in zip(z, w))

        grid_points = list(product((Q(-1), Q(-1, 3), Q(0), Q(2, 3), Q(1)), repeat=2))
        for z in grid_points:
            rz = retract_ball(z)
            self.assertLessEqual(sqdist(rz, (0, 0)), 1)
            if sqdist(z, (0, 0)) <= 1:
                self.assertEqual(rz, z)
            for w in grid_points:
                self.assertLessEqual(sqdist(rz, retract_ball(w)), sqdist(z, w))
        samples = sample_cube(2, 9, disk_map_on_square)
        cell = find_cube_witness(2, 9, samples)
        result = check_cube_witness(2, 9, samples, cell)
        p = retract_ball(tuple(2 * x - 1 for x in result["anchor"]))
        self.assertEqual(p, (Q(1, 3), Q(1, 9)))
        self.assertEqual(sqdist(p, disk_example(p)), Q(5, 324))

    def test_mixed_stage_named_maps(self):
        for d, k in ((0, 1), (1, 3), (2, 1), (3, 0)):
            selection_stages = set()

            def recorded_evaluator(x, s):
                selection_stages.add(s)
                return staged_rotation(x, s)

            witness = find_named_witness(d, k, recorded_evaluator, lambda m: m + 1)
            m = k + 2
            self.assertEqual(selection_stages, {m})
            self.assertEqual(witness.mesh, 2 ** (m + 1))
            tail_values = set()
            for s in (m, m + 1, m + 5):
                result = check_named_tail(witness, staged_rotation, s)
                self.assertEqual(result["anchor"], witness.anchor)
                self.assertLessEqual(result["max_distance_to_cell_samples"], Q(1, 2 ** m))
                self.assertLessEqual(result["residual"], result["residual_bound"])
                self.assertLess(result["residual_bound"], Q(1, 2 ** k))
                tail_values.add(tuple(result["tail_sample"]))
            if d > 0:
                self.assertEqual(len(tail_values), 3)

        witness = find_named_witness(2, 1, staged_rotation, lambda m: m + 1)
        with self.assertRaises(ValueError):
            check_named_tail(witness, staged_rotation, witness.stage - 1)

        def incoherent(x, s):
            if s == witness.stage:
                return staged_rotation(x, s)
            return (1, 0, 0)

        with self.assertRaisesRegex(ValueError, "mixed-stage estimate"):
            check_named_tail(witness, incoherent, witness.stage + 1)

    def test_reject_invalid_inputs(self):
        for bad in ((-1, 2), (1, 1), (Q(1, 2),), (0.5, 0.5)):
            with self.assertRaises(ValueError):
                rational_point(bad, 1)
        with self.assertRaises(ValueError):
            sample_grid(1, 0, lambda x: x)
        samples = sample_grid(2, 5, lambda x: example_map("rotate", x))
        with self.assertRaises(ValueError):
            check_witness(2, 5, samples, Cell((1, 3), (0, 0)))
        with self.assertRaises(ValueError):
            check_witness(2, 5, samples, Cell((0, 0), (1, 0)))


if __name__ == "__main__":
    unittest.main(verbosity=2)
