import copy
import itertools
import random
import unittest

from unknot import DiagramError, Grid, Move, recognize, verify_certificate
from unknot.determinant import determinant
from unknot.grid import exchangeable, moves, successors
from tools.scramble import scramble, stabilize


UN = Grid.from_rows([[0, 1], [0, 1]])
TREFOIL = Grid.from_json({"x": list(range(5)), "o": [2, 3, 4, 0, 1]})
T35 = Grid.from_json({"x": list(range(8)), "o": [3, 4, 5, 6, 7, 0, 1, 2]})


def random_knot(rng, n):
    while True:
        x, o = list(range(n)), list(range(n))
        rng.shuffle(x)
        rng.shuffle(o)
        if any(a == b for a, b in zip(x, o)):
            continue
        grid = Grid.from_rows(list(zip(x, o)))
        if grid.components() == 1:
            return grid


class GridTests(unittest.TestCase):
    def test_validation(self):
        for value in [None, {}, {"rows": []}, {"rows": [[0, 0], [0, 1]]},
                      {"rows": [[0, 1], [0, 2]]},
                      {"rows": [[False, 1], [0, 1]]},
                      {"x": [0, 0], "o": [1, 1]},
                      {"x": [0, 1], "o": [1, 0], "rows": []}]:
            with self.subTest(value=value), self.assertRaises(DiagramError):
                Grid.from_json(value)

    def test_basic_input_and_components(self):
        self.assertEqual(Grid.from_json({"x": [0, 1], "o": [1, 0]}), UN)
        self.assertEqual(TREFOIL.components(), 1)
        self.assertEqual(TREFOIL.crossing_count(), 3)
        link = Grid.from_rows([[0, 1], [0, 1], [2, 3], [2, 3]])
        self.assertEqual(link.components(), 2)
        with self.assertRaises(DiagramError):
            recognize(link)
        self.assertEqual(Grid.from_json(TREFOIL.to_json()), TREFOIL)

    def test_canonicalization_against_brute_force(self):
        rng = random.Random(100)
        for _ in range(60):
            grid = random_knot(rng, rng.randrange(2, 9))
            expected = min((grid.shift(r, c) for r in range(grid.size)
                            for c in range(grid.size)), key=lambda g: g.rows)
            self.assertEqual(grid.canonical(), expected)
            self.assertEqual(expected.canonical(), expected)

    def test_shift_invariance(self):
        for grid in [TREFOIL, T35, scramble(UN, 8, 14)]:
            for r in range(grid.size):
                for c in range(grid.size):
                    shifted = grid.shift(r, c)
                    self.assertEqual(shifted.canonical(), grid.canonical())
                    self.assertEqual(determinant(shifted), determinant(grid))

    def test_exchange_criteria(self):
        self.assertTrue(exchangeable((0, 1), (2, 3)))
        self.assertTrue(exchangeable((0, 3), (1, 2)))
        self.assertFalse(exchangeable((0, 2), (1, 3)))
        self.assertFalse(exchangeable((0, 1), (1, 2)))
        self.assertFalse(exchangeable((0, 1), (0, 1)))
        with self.assertRaises(DiagramError):
            Move("row_exchange", 0).apply(TREFOIL)
        with self.assertRaises(DiagramError):
            Move("destabilize", 0, 0).apply(UN)
        with self.assertRaises(DiagramError):
            Move("row_exchange", -1).apply(UN)
        with self.assertRaises(DiagramError):
            Move.from_json({"kind": "row_exchange", "index": True})

    def test_all_stabilization_inverses(self):
        for grid in [UN, TREFOIL, T35]:
            for r, pair in enumerate(grid.rows):
                for c in pair:
                    for ar, ac in itertools.product((False, True), repeat=2):
                        larger = stabilize(grid, r, c, ar, ac)
                        self.assertEqual(larger.components(), 1)
                        self.assertEqual(determinant(larger), determinant(grid))
                        restored = Move("destabilize", r + int(ar), c + int(ac)).apply(larger)
                        self.assertEqual(restored, grid)

    def test_random_move_invariants(self):
        rng = random.Random(1709)
        count = 0
        for _ in range(220):
            grid = random_knot(rng, rng.randrange(3, 10))
            value = determinant(grid)
            self.assertEqual(value % 2, 1)
            for move in moves(grid):
                changed = move.apply(grid)
                count += 1
                self.assertEqual(changed.components(), 1)
                self.assertEqual(determinant(changed), value, (grid, move))
                if move.kind != "destabilize":
                    self.assertEqual(move.apply(changed), grid)
        self.assertGreater(count, 1000)

    def test_successors_respect_shift_quotient(self):
        rng = random.Random(52)
        for _ in range(35):
            grid = random_knot(rng, rng.randrange(3, 9))
            expected = {child for child, _ in successors(grid.canonical())}
            expected.add(grid.canonical())
            shifted = grid.shift(rng.randrange(grid.size), rng.randrange(grid.size))
            actual = {child for child, _ in successors(shifted)}
            actual.add(shifted.canonical())
            self.assertEqual(actual, expected)

    def test_exhaustive_grids_through_size_four(self):
        cases = 0
        for n in range(2, 5):
            seen = set()
            for x in itertools.permutations(range(n)):
                for o in itertools.permutations(range(n)):
                    if any(a == b for a, b in zip(x, o)):
                        continue
                    grid = Grid.from_rows(list(zip(x, o)))
                    if grid in seen or grid.components() != 1:
                        continue
                    seen.add(grid)
                    cases += 1
                    result = recognize(grid, use_determinant=False)
                    self.assertEqual(result["verdict"], "UNKNOT", grid)
                    self.assertEqual(verify_certificate(result["certificate"], grid)["verdict"],
                                     "UNKNOT")
        self.assertEqual(cases, 79)

    def test_scrambled_unknots(self):
        for seed in range(12):
            grid = scramble(UN, 8, seed)
            result = recognize(grid, max_states=10000, use_determinant=False)
            self.assertEqual(result["verdict"], "UNKNOT", seed)
            self.assertTrue(verify_certificate(result["certificate"], grid)["valid"])

    def test_known_knots_and_determinant_one(self):
        for grid in [TREFOIL, T35]:
            result = recognize(grid, use_determinant=False)
            self.assertEqual(result["verdict"], "KNOTTED")
            self.assertEqual(result["method"], "closed_monotone_state_space")
            self.assertTrue(verify_certificate(result["certificate"], grid)["valid"])
        self.assertEqual(determinant(T35), 1)
        self.assertEqual(recognize(T35)["verdict"], "KNOTTED")
        self.assertEqual(recognize(TREFOIL)["method"], "determinant")

    def test_nontrivial_closed_set(self):
        grid = scramble(TREFOIL, 7, 3)
        result = recognize(grid, max_states=10000, use_determinant=False)
        self.assertEqual(result["verdict"], "KNOTTED")
        self.assertGreater(result["states_seen"], 1)
        self.assertTrue(verify_certificate(result["certificate"], grid)["valid"])

    def test_limits_do_not_mean_knotted(self):
        grid = Grid.from_rows([[0, 1], [1, 2], [0, 2]])
        result = recognize(grid, max_states=1, use_determinant=False)
        self.assertEqual(result["verdict"], "UNKNOWN")
        self.assertNotIn("certificate", result)
        self.assertEqual(recognize(grid, timeout=1e-100)["verdict"], "UNKNOWN")
        for limit in (0, -1, True):
            with self.assertRaises(ValueError):
                recognize(UN, max_states=limit)
        for limit in (0, -1, float("nan"), float("inf"), True):
            with self.assertRaises(ValueError):
                recognize(UN, timeout=limit)

    def test_certificate_tampering(self):
        result = recognize(scramble(UN, 6, 4), use_determinant=False)
        good = result["certificate"]
        bad = copy.deepcopy(good)
        bad["moves"] = []
        with self.assertRaises(DiagramError):
            verify_certificate(bad)
        bad = copy.deepcopy(good)
        bad["moves"][0]["index"] = -1
        with self.assertRaises(DiagramError):
            verify_certificate(bad)
        with self.assertRaises(DiagramError):
            verify_certificate(good, UN)
        bad = recognize(TREFOIL)["certificate"]
        bad["value"] = 1
        with self.assertRaises(DiagramError):
            verify_certificate(bad)
        bad = recognize(TREFOIL, use_determinant=False)["certificate"]
        bad["states"].append(UN.to_json())
        with self.assertRaises(DiagramError):
            verify_certificate(bad)
        bad = {"format": "unknot-grid-certificate-v1", "input":
               Grid.from_rows([[0, 1], [1, 2], [0, 2]]).canonical().to_json(),
               "kind": "closed_set", "states": []}
        bad["states"] = [bad["input"]]
        with self.assertRaises(DiagramError):
            verify_certificate(bad)

class VerifierIndependenceTests(unittest.TestCase):
    def test_omitted_search_moves_are_detected(self):
        from unittest.mock import patch
        grid = Grid.from_rows([[0, 1], [1, 2], [0, 2]])
        # Inject a bug in the search's move generator, but not the legal-move kernel.
        with patch("unknot.recognize.successors", return_value=iter(())):
            broken = recognize(grid, use_determinant=False)
        self.assertEqual(broken["verdict"], "KNOTTED")
        with self.assertRaises(DiagramError):
            verify_certificate(broken["certificate"])

    def test_suppressed_certificates(self):
        for grid in [UN, TREFOIL]:
            result = recognize(grid, use_determinant=False, include_certificate=False)
            self.assertNotIn("certificate", result)
