import json
from pathlib import Path
import unittest

from unknot.pattern import PatternError, classify_ball_pattern

EXAMPLES = Path(__file__).resolve().parents[1] / 'examples'


class PatternTests(unittest.TestCase):
    def test_empty_and_simple_circles(self):
        for circles, expected in [(0, True), (1, True), (2, False), (100, False)]:
            self.assertEqual(classify_ball_pattern([], circles).essential_on_ball, expected)

    def test_theta_graph_k3_exception(self):
        answer = classify_ball_pattern([[1, 2, 3], [-1, -3, -2]])
        self.assertTrue(answer.essential_on_ball)
        self.assertEqual(answer.reason, 'dual_is_K3')

    def test_tetrahedron_and_cube(self):
        for name in ['tetrahedron', 'cube']:
            value = json.loads((EXAMPLES / f'pattern_{name}.json').read_text())
            self.assertTrue(classify_ball_pattern(value['vertices']).essential_on_ball)

    def test_prism_separating_triangle(self):
        data = json.loads((EXAMPLES / 'pattern_triangular_prism.json').read_text())
        result = classify_ball_pattern(data['vertices'])
        self.assertFalse(result.essential_on_ball)
        self.assertEqual(result.reason, 'dual_separator')
        self.assertEqual(len(result.witness['separator']), 3)

    def test_bridge(self):
        result = classify_ball_pattern([[1, -1, 2], [-2, 3, -3]])
        self.assertFalse(result.essential_on_ball)
        self.assertEqual(result.reason, 'dual_loop')

    def test_two_edge_cut(self):
        vertices = [[1, 2, 3], [-1, 4, -2], [-4, 5, 6], [-5, -3, -6]]
        result = classify_ball_pattern(vertices)
        self.assertFalse(result.essential_on_ball)
        self.assertEqual(result.reason, 'dual_parallel_edges')

    def test_disconnected_graph_and_circle(self):
        graph = [[1, 2, 3], [-1, -3, -2]]
        self.assertFalse(classify_ball_pattern(graph, 1).essential_on_ball)
        graph += [[4, 5, 6], [-4, -6, -5]]
        self.assertEqual(classify_ball_pattern(graph).reason, 'disconnected_pattern')

    def test_surface_genus_checked(self):
        with self.assertRaisesRegex(PatternError, 'non-spherical'):
            classify_ball_pattern([[1, 2, 3], [-1, -2, -3]])

    def test_malformed(self):
        for value in [None, {}, [[1, 2]], [[1, 2, 0]], [[1, 2, True]],
                      [[1, 2, 3], [-1, -2, 3]], [[1, 2, 3]]]:
            with self.subTest(value=value), self.assertRaises(PatternError):
                classify_ball_pattern(value)
        with self.assertRaises(PatternError):
            classify_ball_pattern([], True)

    def test_global_reflection_preserves_result(self):
        for path in EXAMPLES.glob('pattern_*.json'):
            vertices = json.loads(path.read_text())['vertices']
            self.assertEqual(classify_ball_pattern(vertices).essential_on_ball,
                             classify_ball_pattern([list(reversed(row)) for row in vertices])
                             .essential_on_ball)

    def test_hypothesis_explicit_in_result(self):
        answer = classify_ball_pattern([]).to_json()
        self.assertIn('already known', answer['required_hypothesis'])
        self.assertFalse(answer['constructs_embedded_violating_disc'])


if __name__ == '__main__':
    unittest.main()
