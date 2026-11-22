"""Run small exact examples and adversarial checks; write one JSON report."""
import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from finite_presentations import (Envelope, anchored, eps, evaluate_formula,
                                  function_distance, grid, left_sum,
                                  power_series_cutoffs, select_envelope,
                                  sup_distance, tent)


def main() -> dict:
    out = {"arithmetic": "fractions.Fraction; no floating point",
           "status": "passed", "scope": "finite executable checks, not proofs"}

    # Smooth and nonsmooth targets, all with elementary 1-Lipschitz proofs.
    functions = {"quadratic": lambda x: x[0] * (1 - x[0]),
                 "tent": lambda x: tent(x[0]),
                 "negative_linear": lambda x: -x[0]}
    envelope_results = []
    probe = grid(1, 7)
    for name, f in functions.items():
        for k in (0, 2, 4):
            center, meta = select_envelope(lambda x, p: f(x), k)
            observed = max(abs(center(x) - f(x)) for x in probe)
            radius = F(meta["proved_radius"])
            assert observed <= radius
            envelope_results.append({"target": name, **meta,
                                     "largest_probed_error": str(observed),
                                     "note": "continuum bound is Lemma Envelope bounds"})
    out["selected_envelopes"] = envelope_results

    # An inconsistent table still generates a legal 1-Lipschitz center.
    points = grid(1, 1)
    center = Envelope(points, (F(1), F(-1), F(1)), F(1), F(1))
    probes = grid(1, 4)
    for x, y in product(probes, repeat=2):
        assert abs(center(x) - center(y)) <= sup_distance(x, y)
    out["inconsistent_table"] = {"samples": ["1", "-1", "1"],
                                  "pair_checks": len(probes)**2,
                                  "result": "clipped envelope remains 1-Lipschitz"}

    z, err = function_distance(lambda x: tent(x[0]), lambda x: -tent(x[0]), 1, 5, F(1))
    assert z == 1 and abs(z - F(1)) <= err
    out["function_distance"] = {"finite_score": str(z), "error_allowance": str(err),
                                 "known_exact_distance": "1"}

    # A genuinely alternating continuous sentence.
    atoms = {"distance": lambda x, y: abs(x - y), "tent": tent}
    radius_formula = ("inf", ("sup", ("atom", "distance", (1, 0))))
    results = []
    for m in range(1, 5):
        carrier = tuple(p[0] for p in grid(1, m))
        value = evaluate_formula(radius_formula, carrier, atoms)
        assert value == F(1, 2)
        results.append({"mesh_index": m, "value": str(value)})
    out["inf_x_sup_y_distance"] = results

    # Total correspondence with sharp nonzero error, matching the Lean example.
    left, right = (F(0), F(1)), (F(0), F(1, 2), F(1))
    relation = {(a, b) for a in left for b in right if abs(a - b) <= F(1, 2)}
    assert all(any((a, b) in relation for b in right) for a in left)
    assert all(any((a, b) in relation for a in left) for b in right)
    atom_error = max(abs(tent(a) - tent(b)) for a, b in relation)
    sentence = ("sup", ("atom", "tent", (0,)))
    va = evaluate_formula(sentence, left, atoms)
    vb = evaluate_formula(sentence, right, atoms)
    assert abs(va - vb) == atom_error == F(1, 2)
    out["sharp_transfer"] = {"atomic_error": str(atom_error),
                             "left_value": str(va), "right_value": str(vb),
                             "sentence_error": str(abs(va - vb))}

    # Exact optimizer over an explicitly described infinite class.
    identities = []
    for m in range(1, 9):
        n = 2**m
        numerator = sum(min(j, n - j) for j in range(n))
        assert numerator == (n // 2)**2
        assert left_sum(tent, n) == F(1, 4)
        identities.append({"cells": n, "numerator": numerator, "integral": "1/4"})
    out["tent_identities"] = identities
    catalog_values = []
    for table in product((F(-1), F(0), F(1)), repeat=3):
        env = Envelope(grid(1, 1), table, F(1), F(1))
        f = anchored(lambda x, env=env: env((x,)))
        catalog_values.append(left_sum(f, 16))
    assert max(catalog_values) == F(1, 4)
    out["small_function_catalog"] = {"centers": len(catalog_values),
                                      "maximum_grid_integral": str(max(catalog_values)),
                                      "note": "coarse illustration, not enumeration of the full precision net"}
    D, J = F(1), F(1, 2)  # f=-tent
    assert D**2 == 2 * J
    out["sharp_residual_bound"] = {"function": "-tent", "distance": str(D),
                                    "objective_gap": str(J), "D_squared_equals_2J": True}

    # Check the stated analytic cutoffs against exact geometric majorants.
    cutoff_results = []
    for rho in (F(1, 4), F(1, 2), F(3, 4)):
        for k in (0, 3, 8):
            c = power_series_cutoffs(F(1), F(1), rho, k)
            assert c["value_tail_bound"] <= eps(k + 1)
            assert c["derivative_tail_bound"] <= eps(k + 1)
            cutoff_results.append({"rho": str(rho), "precision": k,
                                   **{key: str(value) for key, value in c.items()}})
    out["analytic_cutoffs"] = cutoff_results
    return out


if __name__ == "__main__":
    target = Path(__file__).resolve().parents[1] / "validation" / "examples.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    report = main()
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Exact-rational examples passed; report: {target.name}")
