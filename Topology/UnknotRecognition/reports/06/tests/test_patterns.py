from copy import deepcopy
import json
from pathlib import Path
import unittest

from unknot.patterns import BallPattern, classify_pattern, verify_violating_witness

ROOT = Path(__file__).resolve().parents[1]


def pattern(name):
    return BallPattern.from_json(json.loads((ROOT/'examples'/f'pattern-{name}.json').read_text()))


class PatternTests(unittest.TestCase):
    def test_empty_and_single_circle(self):
        for name in ('empty', 'circle'):
            self.assertEqual(classify_pattern(pattern(name))['status'], 'essential')

    def test_disconnected_circles(self):
        p = pattern('two-circles')
        r = classify_pattern(p)
        self.assertEqual(r['witness']['intersections'], 0)
        self.assertTrue(verify_violating_witness(p, r['witness']))

    def test_disconnected_graphs(self):
        theta = pattern('theta')
        p = BallPattern(theta.rotation + tuple(tuple(d+6 for d in v) for v in theta.rotation))
        r = classify_pattern(p)
        self.assertTrue(verify_violating_witness(p, r['witness']))
        self.assertEqual(r['witness']['intersections'], 0)

    def test_circle_plus_graph(self):
        p = BallPattern(pattern('theta').rotation, 1)
        self.assertEqual(classify_pattern(p)['status'], 'violating')

    def test_single_edge_bond(self):
        p = pattern('dumbbell')
        r = classify_pattern(p)
        self.assertEqual(r['witness']['intersections'], 1)
        self.assertTrue(verify_violating_witness(p, r['witness']))

    def test_two_edge_bond(self):
        p = pattern('double-theta')
        r = classify_pattern(p)
        self.assertEqual(r['witness']['intersections'], 2)
        self.assertTrue(verify_violating_witness(p, r['witness']))

    def test_nontrivial_three_edge_bond(self):
        p = pattern('prism')
        r = classify_pattern(p)
        self.assertEqual(r['witness']['intersections'], 3)
        self.assertEqual([len(s) for s in r['witness']['vertex_sides']], [3, 3])
        self.assertTrue(verify_violating_witness(p, r['witness']))

    def test_tripods_are_not_violations(self):
        for name in ('theta', 'tetrahedron', 'cube'):
            self.assertEqual(classify_pattern(pattern(name))['status'], 'essential')

    def test_embedding_orientation_independence(self):
        for name in ('theta', 'tetrahedron', 'prism', 'cube', 'double-theta'):
            p = pattern(name)
            opposite = BallPattern(tuple(tuple(reversed(v)) for v in p.rotation), p.circles)
            self.assertEqual(classify_pattern(p)['status'], classify_pattern(opposite)['status'])

    def test_bad_witnesses_rejected(self):
        p = pattern('prism')
        good = classify_pattern(p)['witness']
        for key, value in [('cut_edges', [0]), ('intersections', 2), ('vertex_sides', [[0], [1]]),
                           ('kind', 'nonexistent')]:
            bad = deepcopy(good)
            bad[key] = value
            self.assertFalse(verify_violating_witness(p, bad))

    def test_ambient_precondition_is_explicit(self):
        for ambient in (None, 'sphere boundary', 'arbitrary 3-manifold'):
            with self.assertRaises(ValueError):
                BallPattern.from_json({'ambient': ambient, 'rotation': []})

    def test_invalid_rotation_systems(self):
        for rotation in ([[0,1,2]], [[0,1,1],[2,3,4]], [[True,1,2],[3,4,5]],
                         [[0,2,4],[1,3,5]]):
            with self.subTest(rotation=rotation), self.assertRaises(ValueError):
                BallPattern.from_json({'ambient':'3-ball','rotation':rotation})

    def test_invalid_circle_count(self):
        for circles in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                BallPattern.from_json({'ambient':'3-ball','rotation':[],'circles':circles})


if __name__ == '__main__':
    unittest.main()
