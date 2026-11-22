#!/usr/bin/env python3
"""Reproducible numerical cross-checks of the cuboid extremal formulas.

The analytic calculator in cuboid.py is compared against the independent
all-simple-face-chain unfolding routine in unfold_verify.py.  Additional
checks compare the four-image vertex formula and five-image antipodal formula
at deterministic pseudorandom face points, not just their maximizing points.

No result here substitutes for the mathematical proof.  Decimal root brackets
are numerical brackets and the unfolding check uses binary floating point;
neither is a certified interval-arithmetic computation.  The JSON records the
seed, input cases, count, tolerance, and largest discrepancy.
"""

from __future__ import annotations

from decimal import Decimal
import json
import math
from pathlib import Path
import random

from cuboid import antipodal_squared_distances, solve, vertex_face_squared_distances
from unfold_verify import self_test, shortest_path


SEED = 20261119
BOXES = [
    (1, 1, 1),
    (1, 1, 1.4),
    (1, 1, 1.4142135623730951),
    (1, 1, 1.5),
    (1, 1, 2),
    (1, 1, 10),
    (1, 2, 2),
    (1, 2, 3),
    (1, 2, 10),
    (0.1, 1, 1.1),
    (0.1, 1, 5),
    (2, 3, 4),
    (3, 4, 5),
    (14, 16, 18),
    (2, 2.1, 3),
    (0.5, 1, 1.2),
    (5, 3, 4),  # verifies mapping back from sorted axes
    (0.03, 0.8, 3),
]


def run() -> dict:
    rng = random.Random(SEED)
    records = []
    maximum_error = 0.0
    maximum_scaled_error = 0.0
    maximum_path_length_error = 0.0

    def compare(label, sides, p, q, expected):
        nonlocal maximum_error, maximum_scaled_error, maximum_path_length_error
        expected = float(expected)
        p, q = tuple(map(float, p)), tuple(map(float, q))
        actual = shortest_path(sides, p, q)
        error = abs(actual.distance - expected)
        scale = max(max(sides), abs(expected), 1.0)
        scaled = error / scale
        if scaled > 3e-10:
            raise AssertionError(f"{label}: formula {expected}, unfolding {actual.distance}")
        points = (actual.start, *actual.crossing_points, actual.end)
        reconstructed = sum(math.dist(u, v) for u, v in zip(points, points[1:]))
        path_error = abs(reconstructed - actual.distance)
        if path_error / scale > 3e-10:
            raise AssertionError(f"{label}: lifted path length disagrees with development")
        maximum_error = max(maximum_error, error)
        maximum_scaled_error = max(maximum_scaled_error, scaled)
        maximum_path_length_error = max(maximum_path_length_error, path_error)
        records.append({
            "case": label,
            "sides": sides,
            "X": p,
            "Y": q,
            "formula_distance": expected,
            "independent_unfolding_distance": actual.distance,
            "absolute_error": error,
            "chosen_face_chain": actual.face_chain,
            "valid_simple_chains": actual.valid_chain_count,
        })

    known_tests = self_test()
    for index, sides in enumerate(BOXES):
        result = solve(*sides)
        for key in ("fixed_vertex", "free_endpoints"):
            witness = result[key]
            compare(f"box_{index:02d}_{key}_witness", sides,
                    witness["X"], witness["Y"], witness["distance"])
        a, b, c = sorted(Decimal(str(x)) for x in sides)
        sorted_sides = tuple(map(float, (a, b, c)))
        for sample in range(5):
            # Deliberately sample all the top face for the vertex formula.
            x, y = a * Decimal(str(rng.random())), b * Decimal(str(rng.random()))
            expected = min(vertex_face_squared_distances(a, b, c, x, y)).sqrt()
            compare(f"box_{index:02d}_top_face_{sample}", sorted_sides,
                    (0, 0, 0), (x, y, c), expected)
            # Coordinate reflections reduce antipodal points to a quarter-face.
            x = a * Decimal(str(rng.random())) / 2
            y = b * Decimal(str(rng.random())) / 2
            expected = min(antipodal_squared_distances(a, b, c, x, y)).sqrt()
            compare(f"box_{index:02d}_antipodal_{sample}", sorted_sides,
                    (x, y, 0), (a - x, b - y, c), expected)

    return {
        "status": "passed",
        "purpose": "Numerical cross-validation of distinct algorithms; not a proof certificate.",
        "seed": SEED,
        "box_count": len(BOXES),
        "independent_comparison_count": len(records),
        "known_answer_self_test_count": len(known_tests),
        "unfolding_tolerance_relative_to_largest_side": 1e-10,
        "comparison_tolerance_scaled": 3e-10,
        "max_absolute_distance_error": maximum_error,
        "max_scaled_distance_error": maximum_scaled_error,
        "max_lifted_path_length_error": maximum_path_length_error,
        "known_answer_self_tests": [
            {"case": test["name"], "expected": test["expected"], "actual": test["distance"]}
            for test in known_tests
        ],
        "comparisons": records,
    }


def main():
    result = run()
    output = Path(__file__).resolve().parent.parent / "verification" / "numerical_checks.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ("comparisons", "known_answer_self_tests")}, indent=2))


if __name__ == "__main__":
    main()
