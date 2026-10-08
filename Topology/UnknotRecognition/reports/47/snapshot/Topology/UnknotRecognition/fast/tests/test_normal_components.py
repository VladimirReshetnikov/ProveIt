"""Native compressed topology: exact certificates, huge inputs and failure paths."""

from copy import deepcopy
import json
from unittest.mock import patch
import unittest

from fastunknot.interval_orbits import OrbitLimitExceeded, count_orbits
from fastunknot.normal_components import (
    analyze_normal_surface, cone_pairings, verify_normal_surface_certificate,
)
from fastunknot.normal_interval_extraction import ExtractionError, encode_large_integers
from test_normal_interval_extraction import core_torus, paired_balls


class NormalComponentTests(unittest.TestCase):
    def test_meridian_disk_and_arbitrary_binary_multiplicity(self):
        for multiple in (1, 2, 3, 17, 1 << 12000):
            coordinates = [[multiple, multiple, 0, 0, 0, 0, multiple]]
            result = analyze_normal_surface(core_torus(), coordinates, record_trace=True)
            summary = result["summary"]
            self.assertEqual(summary["components"], multiple)
            self.assertEqual(summary["orientable_components"], multiple)
            self.assertEqual(summary["nonorientable_components"], 0)
            self.assertEqual(summary["boundary_components"], multiple)
            self.assertEqual(summary["closed_components"], 0)
            self.assertEqual(summary["euler_characteristic"], multiple)
            self.assertEqual(summary["boundary_homology_nonzero_mod2"], bool(multiple & 1))
            self.assertEqual(summary["certifies_compressing_disk"], multiple == 1)
            proof = json.loads(json.dumps(encode_large_integers(result["certificate"])))
            self.assertTrue(verify_normal_surface_certificate(core_torus(), coordinates, proof))

    def test_disk_in_ball_has_nullhomologous_boundary(self):
        triangulation = {"tetrahedra": [[None] * 4]}
        for coordinate in range(7):
            row = [0] * 7
            row[coordinate] = 1
            result = analyze_normal_surface(triangulation, [row], record_trace=True)
            summary = result["summary"]
            self.assertTrue(summary["is_disk"])
            self.assertEqual(summary["boundary_components"], 1)
            self.assertFalse(summary["certifies_compressing_disk"])
            self.assertFalse(summary["boundary_homology_nonzero_mod2"])
            self.assertTrue(verify_normal_surface_certificate(
                triangulation, [row], result["certificate"]))

    def test_sharp_mixed_stack_gluing(self):
        coordinates = [[1, 1, 1, 1, 2, 0, 0], [1, 2, 1, 1, 1, 0, 0]]
        result = analyze_normal_surface(paired_balls(), coordinates, record_trace=True)
        summary = result["summary"]
        self.assertEqual(summary["components"], 7)
        self.assertEqual(summary["euler_characteristic"], 7)
        self.assertEqual(summary["boundary_components"], 7)
        self.assertEqual(summary["orientable_components_with_boundary"], 7)
        self.assertTrue(verify_normal_surface_certificate(
            paired_balls(), coordinates, result["certificate"]))

    def test_coning_counts_touched_orbits_not_marked_points(self):
        size = 100
        original = [{"start": 0, "stop": 80, "sign": 1, "offset": 20}]
        self.assertEqual(count_orbits(size, original), 20)
        for marked, expected in (([], 0), ([(0, 1), (20, 21)], 1),
                                 ([(0, 3), (20, 23)], 3), ([(10, 60)], 20)):
            coned, nonempty = cone_pairings(size, original, marked)
            touched = 20 - count_orbits(size, coned) + 1 if nonempty else 0
            self.assertEqual(touched, expected)
        with self.assertRaises(ValueError):
            cone_pairings(size, original, [(0, 101)])

    def test_empty_surface(self):
        result = analyze_normal_surface(core_torus(), [[0] * 7], record_trace=True)
        summary = result["summary"]
        for key in ("components", "boundary_components", "euler_characteristic",
                    "vertices", "edges", "normal_discs"):
            self.assertEqual(summary[key], 0)
        self.assertFalse(summary["is_disk"])
        self.assertTrue(verify_normal_surface_certificate(
            core_torus(), [[0] * 7], result["certificate"]))

    def test_replay_does_not_call_the_producer(self):
        tri, coords = core_torus(), [[1, 1, 0, 0, 0, 0, 1]]
        certificate = analyze_normal_surface(tri, coords, record_trace=True)["certificate"]
        with patch("fastunknot.normal_components.analyze_orbits", side_effect=AssertionError), \
                patch("fastunknot.interval_orbits.analyze_orbits", side_effect=AssertionError):
            self.assertTrue(verify_normal_surface_certificate(tri, coords, certificate))

    def test_forged_certificates_and_input_binding(self):
        tri, coords = core_torus(), [[1, 1, 0, 0, 0, 0, 1]]
        proof = analyze_normal_surface(tri, coords, record_trace=True)["certificate"]
        mutations = []
        bad = deepcopy(proof)
        bad["summary"]["components"] = True
        mutations.append(bad)
        bad = deepcopy(proof)
        bad["summary"]["certifies_compressing_disk"] = False
        mutations.append(bad)
        bad = deepcopy(proof)
        bad["boundary_homology"]["cycle_edges"] = []
        mutations.append(bad)
        bad = deepcopy(proof)
        bad["queries"]["components"]["orbit_count"] = 0
        mutations.append(bad)
        bad = deepcopy(proof)
        bad["queries"]["extra"] = {}
        mutations.append(bad)
        for certificate in mutations:
            self.assertFalse(verify_normal_surface_certificate(tri, coords, certificate))
        self.assertFalse(verify_normal_surface_certificate(
            tri, [[2, 2, 0, 0, 0, 0, 2]], proof))

    def test_cancellation_limits_and_invalid_input(self):
        tri, coords = core_torus(), [[1, 1, 0, 0, 0, 0, 1]]
        proof = analyze_normal_surface(tri, coords, record_trace=True)["certificate"]
        class Cancelled(Exception):
            pass
        def stop():
            raise Cancelled()
        with self.assertRaises(Cancelled):
            analyze_normal_surface(tri, coords, check=stop)
        with self.assertRaises(Cancelled):
            verify_normal_surface_certificate(tri, coords, proof, check=stop)
        with self.assertRaises(OrbitLimitExceeded):
            analyze_normal_surface(tri, coords, max_cycles=0)
        with self.assertRaises(ExtractionError):
            analyze_normal_surface(tri, [[True, 1, 0, 0, 0, 0, 1]])
        with self.assertRaises(ValueError):
            analyze_normal_surface(tri, coords, record_trace=1)


if __name__ == "__main__":
    unittest.main()
