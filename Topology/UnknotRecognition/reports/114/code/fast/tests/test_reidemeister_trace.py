"""RIII certificates must distinguish faces sharing the same crossings."""
import itertools
import json
import random
import unittest

from fastunknot.diagram import Diagram
from fastunknot.simplify import Move, _Darts, replay, simplify


class ReidemeisterTraceTests(unittest.TestCase):
    def test_two_faces_on_the_same_crossings(self):
        diagram = Diagram.from_braid(2, [1, 1, -1])
        cases = [
            ((11, 4, 0), ((0, 1, 2, 0), (3, 4, 1, 3), (2, 4, 5, 5))),
            ((9, 2, 6), ((0, 1, 1, 2), (3, 4, 4, 0), (5, 5, 3, 2))),
        ]
        for face, expected in cases:
            for permutation in itertools.permutations(face):
                move = Move("R3", (0, 1, 2), permutation)
                self.assertEqual(replay(diagram, [move]).pd, expected)
                saved = json.loads(json.dumps([move.to_json()]))
                self.assertEqual(replay(diagram, saved).pd, expected)
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            replay(diagram, [Move("R3", (0, 1, 2))])

    def test_invalid_records_are_rejected(self):
        diagram = Diagram.from_braid(2, [1, 1, -1])
        invalid = [
            {}, {"kind": "R4", "crossings": [0, 1, 2]},
            {"kind": "R3", "crossings": [False, 1, 2]},
            {"kind": "R3", "crossings": [0.0, 1, 2]},
            {"kind": "R3", "crossings": [0, 1, 1]},
            {"kind": "R3", "crossings": [0, 1]},
            {"kind": "R3", "crossings": [0, 1, 3]},
            {"kind": "R1", "crossings": [0], "triangle": [0]},
        ]
        for face in ([11, 4, False], [11.0, 4, 0], [12, 4, 0], [-1, 4, 0],
                     [11, 4, 1], [11, 4, 4], [11, 4], 3):
            invalid.append({"kind": "R3", "crossings": [0, 1, 2], "triangle": face})
        for record in invalid:
            with self.subTest(record=record), self.assertRaises(ValueError):
                replay(diagram, [record])

    def test_every_face_of_generated_diagrams(self):
        rng = random.Random(2701)
        count = unique = ambiguous = 0
        for _ in range(400):
            strands = rng.randrange(2, 6)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(3, 19))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:  # only single-component closures are inputs
                continue
            state = _Darts(diagram)
            faces = {frozenset(t): t for d in range(4 * diagram.crossings)
                     if (t := state.triangle_at(d)) is not None}
            groups = {}
            for face in faces.values():
                crossings = tuple(sorted(d // 4 for d in face))
                groups.setdefault(crossings, []).append(face)
            for crossings, triangles in groups.items():
                for triangle in triangles:
                    changed = _Darts(diagram)
                    if changed.apply_r3(triangle) is None:
                        with self.assertRaises(ValueError):
                            replay(diagram, [Move("R3", crossings, triangle)])
                        continue
                    expected = changed.rebuild().pd
                    Diagram.from_pd(expected)  # independent full PD validation
                    self.assertEqual(replay(diagram, [Move("R3", crossings, triangle)]).pd,
                                     expected)
                    count += 1
                    if len(triangles) == 1:
                        self.assertEqual(replay(diagram, [Move("R3", crossings)]).pd, expected)
                        unique += 1
                if len(triangles) > 1:
                    with self.assertRaisesRegex(ValueError, "ambiguous"):
                        replay(diagram, [Move("R3", crossings)])
                    ambiguous += 1
        self.assertGreater(count, 80)
        self.assertGreater(unique, 20)
        self.assertGreater(ambiguous, 0)

    def test_input_darts_survive_prior_deletions_and_json_roundtrip(self):
        word = [2, -1, 2, -3, -1, 3, -1, -2, -1, 1, 3, -2, 3]
        diagram = Diagram.from_braid(4, word)
        reduced, trace = simplify(diagram)
        self.assertEqual(reduced.crossings, 0)
        first_r3 = next(i for i, move in enumerate(trace) if move.kind == "R3")
        self.assertGreater(first_r3, 0)
        removed = {c for move in trace[:first_r3] for c in move.crossings}
        for move in trace:
            if move.kind == "R3":
                self.assertIsNotNone(move.triangle)
                self.assertTrue(removed.isdisjoint(d // 4 for d in move.triangle))
        saved = json.loads(json.dumps([move.to_json() for move in trace]))
        self.assertEqual(replay(diagram, saved).pd, reduced.pd)
        # Every prefix is reproducible, including ones before complete reduction.
        for length in range(1, len(trace) + 1):
            self.assertEqual(replay(diagram, saved[:length]).pd,
                             replay(diagram, trace[:length]).pd)

    def test_move_value_semantics_and_legacy_json(self):
        crossings, face = [0, 1, 2], [11, 4, 0]
        move = Move("R3", crossings, face)
        crossings[0], face[0] = 9, 8
        self.assertEqual(move, Move("R3", (0, 1, 2), (11, 4, 0)))
        self.assertEqual(len({move, Move("R3", (0, 1, 2), (11, 4, 0))}), 1)
        self.assertNotEqual(move, Move("R3", (0, 1, 2), (9, 2, 6)))
        with self.assertRaises(AttributeError):
            move.triangle = (9, 2, 6)
        self.assertEqual(Move("R1", (0,)).to_json(), {"kind": "R1", "crossings": [0]})
        self.assertEqual(replay(Diagram.from_braid(2, [1]),
                                [{"kind": "R1", "crossings": [0]}]).crossings, 0)


if __name__ == "__main__":
    unittest.main()
