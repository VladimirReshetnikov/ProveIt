#!/usr/bin/env python3
from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
import unittest

from conway_core import (
    ConwayDatum,
    convex_intersection,
    det,
    halfturn_path,
    lattice_coordinates,
    load_datum,
    path_J,
    paths_equal,
    polygon_area2,
    reverse_path,
    translate_path,
)

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "zigzag_conway_tile.json"


class ConwayCoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.tile = load_datum(EXAMPLE)

    def test_local_criterion(self) -> None:
        self.assertTrue(all(self.tile.local_checks().values()))

    def test_periods_and_area(self) -> None:
        self.assertEqual(self.tile.t, (Q(1), Q(6)))
        self.assertEqual(self.tile.u, (Q(-11), Q(7)))
        self.assertEqual(det(self.tile.t, self.tile.u), Q(73))
        self.assertEqual(self.tile.doubled_area(), Q(73))
        self.assertTrue(self.tile.area_identity())

    def test_open_path_translation_formula(self) -> None:
        p = self.tile.b
        w = (Q(7, 3), Q(-5, 4))
        lhs = path_J(translate_path(p, w))
        rhs = path_J(p) + det(w, (p[-1][0] - p[0][0], p[-1][1] - p[0][1]))
        self.assertEqual(lhs, rhs)

    def test_halfturn_boundary_pairings(self) -> None:
        self.assertTrue(all(self.tile.orbit_boundary_identities().values()))

    def test_lattice_coordinates(self) -> None:
        t, u = self.tile.t, self.tile.u
        self.assertEqual(lattice_coordinates(t, t, u), (Q(1), Q(0)))
        self.assertEqual(lattice_coordinates(u, t, u), (Q(0), Q(1)))

    def test_torus_certificate(self) -> None:
        cert = self.tile.torus_certificate()
        self.assertEqual(cert["total_area"], Q(1))
        self.assertEqual(cert["positive_overlap_pair_count"], 0)
        self.assertTrue(cert["exact_multiplicity_one"])

    def test_report_is_json_serializable(self) -> None:
        report = self.tile.report()
        json.dumps(report, default=str)
        self.assertTrue(report["torus_certificate"]["exact_multiplicity_one"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
