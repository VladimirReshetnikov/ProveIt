#!/usr/bin/env python3
"""Run finite exact regression checks and regenerate the example tables."""
from __future__ import annotations

import csv
import io
import json
from pathlib import Path
import platform
import sys
import unittest
from fractions import Fraction as F

import test_certified_contractions
from certified_contractions import (
    Q, Q_coherence_budget, coupled_demo, derive_weights, dyadic_decimal,
    neumann_supersolution, no_gap_defect, no_gap_epsilon,
    no_gap_fixed_point, norm_w, sub, tower_adjacent_distance,
    tower_residual, tower_residual_budget,
)


HERE = Path(__file__).resolve().parent


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    if value is None or isinstance(value, (str, int, bool)):
        return value
    raise TypeError(f"unsupported example-data type: {type(value).__name__}")


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(encode(value), indent=2, sort_keys=True) + "\n",
                    encoding="utf-8")


def generate_data() -> dict:
    output = HERE / "data"
    output.mkdir(exist_ok=True)
    model, root = coupled_demo()
    gain = model.gain
    weights = derive_weights(gain.A, 2, F(1, 4))
    rho = (F(1, 100), F(1, 100))
    neumann = []
    for N in range(7):
        z = neumann_supersolution(gain, rho, N)
        neumann.append({"N": N, "z": z.z, "partial_sum": z.partial_sum,
                        "tail": z.tail, "tail_norm": z.tail_norm,
                        "supersolution_slack": z.slack})
    trajectory = []
    for t in range(9):
        x = model.iterate((0, 0), t)
        trajectory.append({"steps": t, "point": x, "residual": model.residual(x),
                           "exact_root_error": norm_w(sub(x, root), gain.w)})

    coordinates = []
    for i in range(4):
        k = 10
        n = i + k + 3
        q = Q(i, k)
        radius = Q_coherence_budget(k)
        low, high = max(F(0), q - radius), min(F(1), q + radius)
        coordinates.append({
            "coordinate": i, "precision": k, "dimension": n,
            "steps": n + 4, "fractional_bits": n + 8,
            "sample": str(q), "sample_decimal_exact": dyadic_decimal(q),
            "interval_radius": str(radius),
            "lower": str(low), "upper": str(high),
            "lower_decimal_exact": dyadic_decimal(low),
            "upper_decimal_exact": dyadic_decimal(high),
            "solver_residual": str(tower_residual(n)),
            "solver_residual_budget": str(tower_residual_budget(n)),
        })
    with (output / "coordinates.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(coordinates[0]))
        writer.writeheader()
        writer.writerows(coordinates)
    write_json(output / "coordinates.json", {
        "arithmetic": "fractions.Fraction and exact integer decimal conversion",
        "interpretation": (
            "Intervals for the infinite fixed coordinate are justified by the "
            "universal tower theorem in the accompanying report; this script "
            "checks the displayed finite computations and residuals only."
        ),
        "radius_formula": "2^(-k-2)",
        "maximum_dimension": 16,
        "rows": coordinates,
    })

    tower = []
    for n in range(1, 17):
        row = {"dimension": n, "steps": n + 4, "bits": n + 8,
               "residual": tower_residual(n),
               "residual_budget": tower_residual_budget(n)}
        if n < 16:
            row["adjacent_restriction_distance"] = tower_adjacent_distance(n)
        tower.append(row)
    counterexample = []
    for n in range(8):
        epsilon = no_gap_epsilon(n)
        counterexample.append({
            "n": n, "contraction_gap": epsilon,
            "contraction_factor": 1 - epsilon,
            "fixed_point": no_gap_fixed_point(n),
            "adjacent_commutation_defect": no_gap_defect(n),
            "defect_over_gap": no_gap_defect(n) / epsilon,
            "adjacent_fixed_point_distance": F(1),
        })
    examples = {
        "status": "finite exact computations, not universal theorem proofs",
        "coupled_affine": {
            "A": gain.A, "w": gain.w, "s": gain.s, "q": gain.q,
            "b": model.b, "lower": model.lower, "upper": model.upper,
            "exact_fixed_point": root,
            "weights_from_power_certificate": {
                "m": weights.m, "theta": weights.theta,
                "A_power_on_ones": weights.power_on_ones,
                "w": weights.certificate.w, "s": weights.certificate.s,
                "q": weights.certificate.q,
            },
            "rho": rho, "neumann_supersolutions": neumann,
            "exact_orbit": trajectory,
        },
        "nonlinear_tower": {
            "update": "a_i + x_i^2/8 + x_(i+1)/8, x_n=0",
            "a_i": "1/(4(i+1))",
            "metric": "max_{i<n} 2^(-i) |x_i-y_i|",
            "q": F(1, 2), "rows": tower,
        },
        "missing_uniform_gap": {
            "map": "(1-epsilon_n)x + epsilon_n c_n",
            "epsilon_n": "2^(-n-2)", "c_n": "n mod 2",
            "rows": counterexample,
        },
    }
    write_json(output / "examples.json", examples)
    return {
        "coordinate_rows": len(coordinates),
        "coordinate_precision": 10,
        "largest_tower_dimension": 16,
        "neumann_horizons": [0, 6],
        "counterexample_rows": len(counterexample),
    }


def main() -> int:
    validation = HERE / "validation"
    validation.mkdir(exist_ok=True)
    suite = unittest.defaultTestLoader.loadTestsFromModule(test_certified_contractions)
    transcript = io.StringIO()
    result = unittest.TextTestRunner(stream=transcript, verbosity=2).run(suite)
    text = transcript.getvalue()
    (validation / "unittest.txt").write_text(text, encoding="utf-8")
    print(text, end="")
    record = {
        "python": platform.python_version(),
        "command": "python3 run_checks.py",
        "arithmetic": "fractions.Fraction; no floating-point inequality checks",
        "passed": result.wasSuccessful(),
        "tests_run": result.testsRun,
        "failures": len(result.failures), "errors": len(result.errors),
        "scope": (
            "Finite regression evidence. Universal correctness and iPRA "
            "formalization are separate obligations stated in the report."
        ),
        "coverage": {
            "gain": "valid asymmetric weights, derived weights, s=1, and malformed certificates",
            "neumann": "N=0 through 12; independent two-dimensional inverse and a three-dimensional case",
            "tower": "dimensions 1 through 16; residuals, adjacent/multilevel restriction, coordinate coherence",
            "equation": "coordinates 0..3 at k=0..9, plus coordinates 0..2 at k=10",
            "negative": "zero dimension, negative horizons, malformed shapes/boxes, inexact input rejection",
            "counterexample": "vanishing commutation defects with alternating exact fixed points",
        },
    }
    if result.wasSuccessful():
        record["generated_data"] = generate_data()
    write_json(validation / "results.json", record)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())

