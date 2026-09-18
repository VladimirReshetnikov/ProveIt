import json
from pathlib import Path
import unittest
from unknot.pattern import BallPattern, assess_pattern

ROOT = Path(__file__).resolve().parents[1]


class PatternTests(unittest.TestCase):
    def test_empty_circle_disconnected(self):
        self.assertTrue(assess_pattern(BallPattern())["essential"])
        self.assertTrue(assess_pattern(BallPattern(circles=1))["essential"])
        self.assertFalse(assess_pattern(BallPattern(circles=2))["essential"])
        theta = ((0, 2, 4), (1, 5, 3))
        self.assertFalse(assess_pattern(BallPattern(theta, 1))["essential"])
        second = tuple(tuple(d + 6 for d in row) for row in theta)
        self.assertFalse(assess_pattern(BallPattern(theta + second))["essential"])

    def test_graph_examples(self):
        for name, expected in [("theta", True), ("tetrahedral", True), ("cube", True),
                               ("dodecahedron", True), ("dumbbell", False),
                               ("triangular_prism", False)]:
            value = json.loads((ROOT / "examples" / f"pattern_{name}.json").read_text())
            pattern = BallPattern.from_json(value)
            result = assess_pattern(pattern)
            self.assertEqual(result["essential"], expected, (name, result))
            self.assertEqual(len(pattern.rotations) - 3 * len(pattern.rotations) // 2
                             + len(pattern.faces()), 2)

    def test_dual_separator_witness(self):
        value = json.loads((ROOT / "examples/pattern_triangular_prism.json").read_text())
        result = assess_pattern(BallPattern.from_json(value))
        self.assertEqual(result["reason"], "dual_vertex_separator")
        self.assertEqual(len(result["witness"]["dual_vertices"]), 3)
        self.assertEqual(len(result["witness"]["remaining_components"]), 2)

    def test_rotation_reversal(self):
        for file in (ROOT / "examples").glob("pattern_*.json"):
            pattern = BallPattern.from_json(json.loads(file.read_text()))
            reverse = BallPattern(tuple(tuple(reversed(row)) for row in pattern.rotations))
            self.assertEqual(assess_pattern(pattern)["essential"],
                             assess_pattern(reverse)["essential"])

    def test_validation(self):
        # Same cyclic order at both theta vertices gives a genus-one embedding.
        for rotations in [((0, 2, 4), (1, 3, 5)), ((0, 2, 4), (1, 5, 5)),
                          ((0, 2, 4),), ((0, 2), (1, 3))]:
            with self.assertRaises(ValueError):
                BallPattern(rotations)
        with self.assertRaises(ValueError):
            BallPattern(circles=-1)
        with self.assertRaises(ValueError):
            BallPattern(circles=True)
        with self.assertRaises(ValueError):
            BallPattern.from_json({"rotations": [5]})
