import itertools
import json
from pathlib import Path
import unittest

from unknot_lab.patterns import (BallPattern, InvalidPattern, decide_ball_pattern,
                                 verify_violation)

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    return BallPattern.from_json(json.loads((ROOT / 'examples' / f'pattern_{name}.json')
                                           .read_text()))


def dual_vertex_connectivity_oracle(pattern):
    """Independent test-only criterion: simple 4-connected dual, or K3/K4.

    This searches vertex cuts of the dual, unlike the production primal-edge
    search. It is not used by the recognizer or the production pattern routine.
    """
    count = len(pattern.components()) + pattern.circle_components
    if count > 1:
        return False
    if not pattern.rotations:
        return True
    faces = pattern.face_cycles()
    owner = {d: i for i, face in enumerate(faces) for d in face}
    adjacency = [set() for _ in faces]
    for e in range(pattern.edge_count):
        a, b = owner[2 * e], owner[2 * e + 1]
        if a == b or b in adjacency[a]:
            return False
        adjacency[a].add(b)
        adjacency[b].add(a)
    n = len(faces)
    if n in (3, 4):
        return all(len(row) == n - 1 for row in adjacency)
    if n < 5:
        return False
    for k in range(4):
        for deleted in itertools.combinations(range(n), k):
            remaining = set(range(n)) - set(deleted)
            seen = {min(remaining)}
            stack = list(seen)
            while stack:
                for w in adjacency[stack.pop()] & remaining - seen:
                    seen.add(w)
                    stack.append(w)
            if seen != remaining:
                return False
    return True


class PatternTests(unittest.TestCase):
    def test_named_patterns(self):
        expected = {'empty': True, 'circle': True, 'theta': True,
                    'tetrahedron': True, 'cube': True, 'dodecahedron': True,
                    'two_circles': False, 'dumbbell': False, 'prism': False,
                    'two_edge_bond': False}
        for name, essential in expected.items():
            with self.subTest(name=name):
                p = load(name)
                result = decide_ball_pattern(p)
                self.assertEqual(result['essential'], essential)
                self.assertEqual(result['ambient_manifold_assumption'], 'known-3-ball')
                self.assertEqual(dual_vertex_connectivity_oracle(p), essential)
                if not essential:
                    self.assertTrue(verify_violation(p, result['certificate']))

    def test_bond_sizes_and_dual_cycles(self):
        for name, size in [('dumbbell', 1), ('two_edge_bond', 2), ('prism', 3)]:
            p = load(name)
            c = decide_ball_pattern(p)['certificate']
            self.assertEqual(len(c['cut_edges']), size)
            self.assertEqual(len(c['dual_cycle']['faces']), size + 1)
            self.assertEqual(c['dual_cycle']['faces'][0], c['dual_cycle']['faces'][-1])
            self.assertEqual(len(set(c['dual_cycle']['faces'][:-1])), size)

    def test_tampered_certificates(self):
        p = load('prism')
        cert = decide_ball_pattern(p)['certificate']
        for field, value in [('shore', []), ('shore', [100]), ('cut_edges', []),
                             ('dual_cycle', {}), ('kind', 'unknown')]:
            with self.subTest(field=field):
                bad = {**cert, field: value}
                self.assertFalse(verify_violation(p, bad))
        for bad in [None, [], 0, {}, {'kind': 'disconnected-pattern', 'components': 2}]:
            self.assertFalse(verify_violation(p, bad))

    def test_circle_plus_graph(self):
        p = load('theta')
        q = BallPattern(p.rotations, 1)
        result = decide_ball_pattern(q)
        self.assertFalse(result['essential'])
        self.assertEqual(result['certificate']['kind'], 'disconnected-pattern')
        self.assertTrue(verify_violation(q, result['certificate']))

    def test_two_graph_components(self):
        p = load('theta')
        q = BallPattern(p.rotations + tuple(tuple(d + 6 for d in row)
                                           for row in p.rotations))
        result = decide_ball_pattern(q)
        self.assertFalse(result['essential'])
        self.assertTrue(verify_violation(q, result['certificate']))

    def test_all_spherical_rotations_against_dual_oracle(self):
        # Enumerate rotations of fixed multigraphs, rejecting nonspherical ones.
        checked = 0
        for name in ['theta', 'dumbbell', 'tetrahedron', 'cube', 'prism', 'two_edge_bond']:
            p = load(name)
            for flips in itertools.product([False, True], repeat=len(p.rotations)):
                rows = tuple(tuple(reversed(row)) if flip else row
                             for row, flip in zip(p.rotations, flips))
                try:
                    q = BallPattern(rows)
                except InvalidPattern:
                    continue
                checked += 1
                result = decide_ball_pattern(q)
                self.assertEqual(result['essential'], dual_vertex_connectivity_oracle(q))
                if not result['essential']:
                    self.assertTrue(verify_violation(q, result['certificate']))
        self.assertGreaterEqual(checked, 14)

    def test_invalid_patterns(self):
        bads = [None, [], {}, {'rotations': None}, {'rotations': [1]},
                {'rotations': [[0, 1]]}, {'rotations': [[0, 1, 2]]},
                {'rotations': [[0, 1, 2], [3, 4, 4]]},
                {'rotations': [[False, 1, 2], [3, 4, 5]]},
                {'rotations': [], 'circle_components': -1},
                {'rotations': [], 'circle_components': True},
                # Theta graph with a torus rotation, not a sphere rotation.
                {'rotations': [[0, 2, 4], [1, 3, 5]]}]
        for obj in bads:
            with self.subTest(obj=obj), self.assertRaises(InvalidPattern):
                BallPattern.from_json(obj)


if __name__ == '__main__':
    unittest.main()
