#!/usr/bin/env python3
"""Regenerate exact normal-coordinate inputs and their compressed extraction."""
import json
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "source/Topology/UnknotRecognition/fast"))
sys.path.insert(0, str(ROOT / "experiments/geometry"))
from fastunknot.normal_interval_extraction import extract_normal_intervals, orbit_input, encode_large_integers
from normal_interval_fixtures import layered_torus


def main():
    destination = ROOT / "examples/normal_intervals"
    destination.mkdir(parents=True, exist_ok=True)
    identity = [0, 1, 2, 3]
    sharp = {"tetrahedra": [
        [{"tetrahedron": 1, "permutation": identity}, None, None, None],
        [{"tetrahedron": 0, "permutation": identity}, None, None, None],
    ]}
    vectors = [[1, 1, 1, 1, 2, 0, 0], [1, 2, 1, 1, 1, 0, 0]]
    layered, meridian = layered_torus(128)
    report = []
    for name, triangulation, coordinates in (
        ("sharp_two_tetrahedra", sharp, vectors),
        ("fibonacci_meridian_128", layered, meridian),
    ):
        raw = {"triangulation": triangulation, "coordinates": coordinates}
        result = extract_normal_intervals(triangulation, coordinates)
        for suffix, payload in (
            ("input", raw), ("extraction", result.as_dict()),
            ("surface_orbits", orbit_input(result)),
            ("orientation_orbits", orbit_input(result, orientation_cover=True)),
        ):
            (destination / (name + "." + suffix + ".json")).write_text(
                json.dumps(encode_large_integers(payload), indent=2) + "\n")
        report.append({"name": name, "statistics": result.as_dict()["statistics"]})
    (destination / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Regenerated two compressed normal-surface examples; no expanded sheets or discs.")


if __name__ == "__main__":
    main()
