from __future__ import annotations

import copy
import random
import unittest

from hierarchy.ball_patterns import (
    BallPattern, PatternError, classify_pattern, verify_violating_witness,
)
from hierarchy import fixtures
from hierarchy.baseline_report06 import patterns as baseline


def baseline_classify(raw):
    # Input->verdict with one baseline validation, including its ordinary
    # serialization path.  Construction alone intentionally does not validate.
    p = baseline.BallPattern(tuple(tuple(row) for row in raw["rotation"]),
                             raw.get("circles", 0))
    return baseline.classify_pattern(p)


class BallPatternsTest(unittest.TestCase):
    def assert_agree(self, raw):
        fast = classify_pattern(raw)
        slow = baseline_classify(raw)
        self.assertEqual(fast["status"], slow["status"])
        if fast["status"] == "violating":
            self.assertTrue(verify_violating_witness(raw, fast["witness"]))
            witness = fast["witness"]
            if witness["kind"] != "disconnected-pattern":
                old_witness = {"kind": "bond",
                               "intersections": witness["intersections"],
                               "cut_edges": sorted(witness["primal_edges"]),
                               "vertex_sides": witness["vertex_sides"]}
                old_pattern = baseline.BallPattern.from_json(raw)
                self.assertTrue(baseline.verify_violating_witness(old_pattern, old_witness))
        else:
            self.assertLessEqual(fast["max_forward_degree"], 5)
            self.assertLessEqual(fast["candidate_pairs"], 10 * max(1, len(raw["rotation"])))
        return fast

    def test_named_examples_and_all_obstruction_types(self):
        cases = [
            (fixtures.triangle(), "essential", None),
            (fixtures.tetrahedron(), "essential", None),
            (fixtures.bipyramid(4), "essential", None),
            (fixtures.bipyramid(8), "essential", None),
            (fixtures.dumbbell(), "violating", "dual-loop"),
            (fixtures.two_edge_bond(), "violating", "dual-bigon"),
            (fixtures.bipyramid(3), "violating", "nonfacial-dual-triangle"),
        ]
        for raw, expected, kind in cases:
            with self.subTest(expected=expected, kind=kind):
                result = self.assert_agree(raw)
                self.assertEqual(result["status"], expected)
                if kind is not None:
                    self.assertEqual(result["witness"]["kind"], kind)

    def test_k3_faces_are_distinct_occurrences(self):
        result = classify_pattern(fixtures.triangle())
        self.assertEqual(result["dual_triangles"], 1)
        self.assertEqual(result["facial_triangles"], 2)
        self.assertEqual(result["distinct_facial_triangles"], 1)
        result = classify_pattern(fixtures.tetrahedron())
        self.assertEqual(result["dual_triangles"], 4)
        self.assertEqual(result["facial_triangles"], 4)
        self.assertEqual(result["distinct_facial_triangles"], 4)

    def test_empty_circle_and_disconnected_inputs(self):
        for circles in (0, 1, 2, 10**1000):
            raw = {"ambient": "3-ball", "rotation": [], "circles": circles}
            result = self.assert_agree(raw)
            self.assertEqual(result["status"], "essential" if circles < 2 else "violating")
        for raw in (
            fixtures.disjoint_union(fixtures.triangle(), fixtures.triangle()),
            fixtures.disjoint_union(fixtures.dumbbell(), fixtures.tetrahedron()),
            fixtures.disjoint_union(fixtures.tetrahedron(), circles=1),
        ):
            result = self.assert_agree(raw)
            self.assertEqual(result["witness"]["intersections"], 0)

    def test_malformed_inputs_and_positive_genus_are_rejected(self):
        malformed = [
            {}, {"rotation": []}, {"ambient": "sphere", "rotation": []},
            {"ambient": "3-ball", "rotation": None},
            {"ambient": "3-ball", "rotation": [[0, 1, 2]]},
            {"ambient": "3-ball", "rotation": [[0, 1], [2, 3]]},
            {"ambient": "3-ball", "rotation": [[0, 1, 2], [3, 4, 4]]},
            {"ambient": "3-ball", "rotation": [[0, 1, 2], [3, 4, 7]]},
            {"ambient": "3-ball", "rotation": [[0, 1, 2], [3, 4, -1]]},
            {"ambient": "3-ball", "rotation": [[True, 1, 2], [3, 4, 5]]},
            {"ambient": "3-ball", "rotation": [[0, 1, 2], [3, 4, 5.0]]},
            {"ambient": "3-ball", "rotation": [], "circles": -1},
            {"ambient": "3-ball", "rotation": [], "circles": True},
            {"ambient": "3-ball", "rotation": [[0, 2, 4], [1, 3, 5]]},
        ]
        for raw in malformed:
            with self.subTest(raw=str(raw)[:100]):
                with self.assertRaises(PatternError):
                    classify_pattern(raw)
        torus = malformed[-1]
        bad_component = fixtures.disjoint_union(fixtures.triangle(), torus)
        with self.assertRaises(PatternError):
            classify_pattern(bad_component)

    def test_exhaustive_two_and_four_vertex_ribbon_maps(self):
        accepted = rejected = 0
        for vertices in (2, 4):
            for matching in fixtures.perfect_matchings(tuple(range(3 * vertices))):
                raw = fixtures.pattern_from_matching(vertices, matching)
                try:
                    BallPattern.from_json(raw)
                except PatternError:
                    rejected += 1
                    with self.assertRaises(ValueError):
                        baseline.BallPattern.from_json(raw)
                    continue
                accepted += 1
                self.assert_agree(raw)
        self.assertEqual(accepted + rejected, 15 + 10395)
        self.assertGreater(accepted, 100)
        self.assertGreater(rejected, 100)

    def test_random_larger_ribbon_maps(self):
        rng = random.Random(729310)
        accepted = 0
        for vertices in (6, 8, 10):
            for _ in range(250):
                raw = fixtures.random_matching_pattern(vertices, rng)
                try:
                    BallPattern.from_json(raw)
                except PatternError:
                    continue
                accepted += 1
                self.assert_agree(raw)
        self.assertGreater(accepted, 50)

    def test_random_spherical_triangulations_with_edge_flips(self):
        for n in range(4, 15):
            for seed in range(5):
                self.assert_agree(fixtures.random_triangulation(n, seed, 10 * n))

    def test_relabeling_rotation_and_mirroring(self):
        examples = [fixtures.triangle(), fixtures.tetrahedron(), fixtures.dumbbell(),
                    fixtures.two_edge_bond(), fixtures.bipyramid(3), fixtures.bipyramid(5)]
        for raw in examples:
            original = classify_pattern(raw)["status"]
            for seed in range(10):
                changed = fixtures.relabel_pattern(raw, seed, mirror=bool(seed % 2))
                self.assertEqual(self.assert_agree(changed)["status"], original)

    def test_witness_corruption_is_rejected(self):
        for raw in [fixtures.dumbbell(), fixtures.two_edge_bond(), fixtures.bipyramid(3)]:
            witness = classify_pattern(raw)["witness"]
            self.assertTrue(verify_violating_witness(raw, witness))
            for bad in [None, [], {}, {"kind": "unknown"}, {"kind": []}]:
                self.assertFalse(verify_violating_witness(raw, bad))
            changes = []
            for key, value in [
                ("kind", "unknown"), ("intersections", 0),
                ("intersections", True), ("dual_vertices", []),
                ("primal_edges", [-1] * witness["intersections"]), ("vertex_sides", []),
            ]:
                bad = copy.deepcopy(witness)
                bad[key] = value
                changes.append(bad)
            bad = copy.deepcopy(witness)
            bad["vertex_sides"][0] = []
            changes.append(bad)
            bad = copy.deepcopy(witness)
            bad["primal_edges"][0] = True
            changes.append(bad)
            for bad in changes:
                self.assertFalse(verify_violating_witness(raw, bad))

    def test_large_full_scan_has_linear_candidate_bound(self):
        ring = 10000
        raw = fixtures.bipyramid(ring)
        result = classify_pattern(raw)
        self.assertEqual(result["status"], "essential")
        self.assertEqual(result["darts"], 6 * ring)
        self.assertEqual(result["dual_triangles"], 2 * ring)
        self.assertLessEqual(result["candidate_pairs"], 10 * (ring + 2))
        self.assertLessEqual(result["max_forward_degree"], 5)


if __name__ == "__main__":
    unittest.main()
