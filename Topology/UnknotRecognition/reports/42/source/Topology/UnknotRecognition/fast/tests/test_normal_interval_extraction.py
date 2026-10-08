"""Small exact regressions for tetrahedral normal interval extraction.

No Regina dependency. The research package contains the larger rational
geometric oracle and independent native component comparisons.
"""

from copy import deepcopy
from itertools import permutations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest

from fastunknot.normal_interval_extraction import (
    ExtractionError, extract_normal_intervals, orbit_input,
)


def paired_balls(permutation=(0, 1, 2, 3), face=0):
    rows = [[None] * 4 for _ in range(2)]
    rows[0][face] = {"tetrahedron": 1, "permutation": list(permutation)}
    rows[1][permutation[face]] = {
        "tetrahedron": 0,
        "permutation": [permutation.index(vertex) for vertex in range(4)],
    }
    return {"tetrahedra": rows}


def core_torus():
    return {"tetrahedra": [[
        {"tetrahedron": 0, "permutation": [1, 2, 3, 0]},
        {"tetrahedron": 0, "permutation": [3, 0, 1, 2]}, None, None,
    ]]}


def small_orbits(data):
    """Finite DSU oracle for small adapter outputs, independent of interval logic."""
    size = data["universe_stop"]
    if size > 1000:
        raise ValueError("small orbit oracle limit")
    parents = list(range(size))

    def root(index):
        while parents[index] != index:
            index = parents[index]
        return index

    for pairing in data["pairings"]:
        for source in range(pairing["start"], pairing["stop"]):
            target = pairing["sign"] * source + pairing["offset"]
            if not 0 <= source < size or not 0 <= target < size:
                raise AssertionError("pairing escapes the universe")
            parents[root(source)] = root(target)
    return len({root(index) for index in range(size)})


class NormalIntervalExtractionTests(unittest.TestCase):
    def test_sharp_local_counts_and_frontier_labels(self):
        coordinates = [[1, 1, 1, 1, 2, 0, 0], [1, 2, 1, 1, 1, 0, 0]]
        result = extract_normal_intervals(paired_balls(), coordinates)
        stats = result.statistics()
        self.assertEqual(stats["surface_face_bands"], 5)
        self.assertEqual(stats["local_residual_cells"], 12)
        self.assertEqual(stats["prism_to_residual_contacts"], 2)
        contacts = [band for band in result.prism_frontier_bands
                    if band.kind == "opposite_residual_cell"]
        self.assertEqual({band.target_tetrahedron for band in contacts}, {0, 1})
        self.assertTrue(all(band.stop == band.start + 1 for band in contacts))
        self.assertTrue(all(band.target_residual_cell == "core_A" for band in contacts))

    def test_reflection_uses_lower_target_disc_for_gap(self):
        raw = paired_balls((2, 3, 0, 1))
        coordinates = [[0, 0, 0, 0, 4, 0, 0]] * 2
        result = extract_normal_intervals(raw, coordinates)
        self.assertEqual(len(result.surface_bands), 1)
        self.assertEqual(len(result.prism_bands), 1)
        surface, prism = result.surface_bands[0], result.prism_bands[0]
        self.assertEqual((surface.start, surface.stop, surface.sign, surface.offset),
                         (0, 4, -1, 3))
        self.assertEqual((prism.start, prism.stop, prism.sign, prism.offset),
                         (0, 3, -1, 2))
        self.assertEqual(small_orbits(orbit_input(result)), 4)

    def test_quadrilateral_transport_under_all_vertex_permutations(self):
        for permutation in permutations(range(4)):
            with self.subTest(permutation=permutation):
                source = [0, 0, 0, 0, 4, 0, 0]
                target = [0] * 7
                mapped_side = {permutation[0], permutation[1]}
                distinguished = mapped_side if 0 in mapped_side else set(range(4)) - mapped_side
                target[3 + next(vertex for vertex in distinguished if vertex != 0)] = 4
                result = extract_normal_intervals(paired_balls(permutation), [source, target])
                band = result.surface_bands[0]
                self.assertEqual(band.sign, 1 if 0 in mapped_side else -1)
                self.assertEqual(small_orbits(orbit_input(result)), 4)
                self.assertEqual(small_orbits(orbit_input(result, orientation_cover=True)), 8)

    def test_meridian_and_disjoint_multiples(self):
        for multiplier in range(1, 7):
            coordinates = [[multiplier, multiplier, 0, 0, 0, 0, multiplier]]
            result = extract_normal_intervals(core_torus(), coordinates)
            self.assertEqual(small_orbits(orbit_input(result)), multiplier)
            self.assertEqual(small_orbits(orbit_input(result, orientation_cover=True)),
                             2 * multiplier)

    def test_huge_hexadecimal_coordinates_remain_compressed(self):
        count = 1 << 65536
        row = [hex(count), hex(count), 0, 0, 0, 0, hex(count)]
        result = extract_normal_intervals(core_torus(), [row])
        self.assertEqual(len(result.stacks), 3)
        self.assertEqual(len(result.surface_bands), 2)
        self.assertEqual(result.statistics()["normal_discs"], 3 * count)
        self.assertEqual(result.statistics()["local_residual_cells"], 4)
        encoded = result.as_dict()
        self.assertIsInstance(encoded["stacks"][0]["count"], str)
        json.dumps(encoded)

    def test_schema_matching_and_quadrilateral_rejections(self):
        raw = core_torus()
        coordinates = [[1, 1, 0, 0, 0, 0, 1]]
        for value in (True, -1, 1.0, "0xgg"):
            bad = deepcopy(coordinates)
            bad[0][0] = value
            with self.subTest(value=value), self.assertRaises(ExtractionError):
                extract_normal_intervals(raw, bad)
        bad = deepcopy(coordinates)
        bad[0][0] += 1
        with self.assertRaises(ExtractionError):
            extract_normal_intervals(raw, bad)
        bad = deepcopy(coordinates)
        bad[0][4] = 1
        with self.assertRaises(ExtractionError):
            extract_normal_intervals(raw, bad)
        bad = deepcopy(raw)
        bad["tetrahedra"][0][0] = None
        with self.assertRaises(ExtractionError):
            extract_normal_intervals(bad, coordinates)
        bad = deepcopy(raw)
        bad["tetrahedra"][0][0]["tetrahedron"] = True
        with self.assertRaises(ExtractionError):
            extract_normal_intervals(bad, coordinates)

    def test_empty_surface_and_cancellation_do_not_mutate_input(self):
        raw = core_torus()
        coordinates = [[1, 1, 0, 0, 0, 0, 1]]
        saved = deepcopy((raw, coordinates))
        class Cancelled(Exception):
            pass
        def check():
            raise Cancelled()
        with self.assertRaises(Cancelled):
            extract_normal_intervals(raw, coordinates, check=check)
        result = extract_normal_intervals(raw, coordinates)
        with self.assertRaises(Cancelled):
            orbit_input(result, check=check)
        self.assertEqual((raw, coordinates), saved)
        empty = extract_normal_intervals(raw, [[0] * 7])
        self.assertEqual(empty.statistics()["local_residual_cells"], 1)
        self.assertEqual(small_orbits(orbit_input(empty)), 0)

    def test_module_cli_has_no_native_dependency(self):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            path.write_text(json.dumps({"triangulation": core_torus(),
                                        "coordinates": [[1, 1, 0, 0, 0, 0, 1]]}))
            command = [sys.executable, "-m", "fastunknot.normal_interval_extraction",
                       str(path), "--orbit-input", "orientation"]
            completed = subprocess.run(command, cwd=Path(__file__).resolve().parents[1],
                                       check=True, capture_output=True, text=True)
            data = json.loads(completed.stdout)
            self.assertEqual(data["universe_stop"], 6)
            self.assertEqual(small_orbits(data), 2)


if __name__ == "__main__":
    unittest.main()
