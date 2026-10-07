#!/usr/bin/env python3
"""Exact checks of displayed combinatorial coefficients and interval models.

This is a finite diagnostic. The general results are proved in the manuscript.
Only the final human-readable decimal endpoints use floating-point arithmetic.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from pathlib import Path
import json


def cube_coefficients():
    cube3 = list(product((0, 1), repeat=3))
    vectors = Counter(
        tuple(sum(cube3[i][j] for i in subset) for j in range(3))
        for subset in combinations(range(8), 4)
    )
    profiles = {}
    for vector, count in vectors.items():
        key = tuple(sorted(abs(v - 2) for v in vector))
        row = profiles.setdefault(key, {"vector_count": 0, "subset_counts": set()})
        row["vector_count"] += 1
        row["subset_counts"].add(count)
    expected = {
        (0, 0, 0): (1, 8), (0, 0, 1): (6, 4), (0, 0, 2): (6, 1),
        (0, 1, 1): (12, 2), (1, 1, 1): (8, 1),
    }
    assert set(profiles) == set(expected)
    for key, (number, multiplicity) in expected.items():
        assert profiles[key] == {
            "vector_count": number, "subset_counts": {multiplicity}
        }
    count_by_splitting = sum(n * n for n in vectors.values())
    cube4 = list(product((0, 1), repeat=4))
    count_directly = sum(
        all(sum(cube4[i][j] for i in subset) == 4 for j in range(4))
        for subset in combinations(range(16), 8)
    )
    assert count_directly == count_by_splitting == 222
    return {
        "balanced_four_cube_subsets": count_directly,
        "split_count": count_by_splitting,
        "three_cube_profiles": [
            {"profile": list(k), "vectors": number, "subsets_per_vector": multiplicity}
            for k, (number, multiplicity) in expected.items()
        ],
    }


def interval_models():
    rows = []
    for n in range(1, 51):
        N = 2 * n + 1
        pair_counts = Counter((x + y) % N for x in range(n) for y in range(n))
        energy = sum(v * v for v in pair_counts.values())
        assert energy == (2 * n**3 + n) // 3
        delta = F(n, N)
        f = tuple(2 * (F(int(x < n)) - delta) for x in range(N))
        correlations = [
            sum((f[x] * f[(x - h) % N] for x in range(N)), F(0)) / N
            for h in range(N)
        ]
        u2_power = sum((c * c for c in correlations), F(0)) / N
        expected_u2 = 16 * (F(energy, N**3) - delta**4)
        assert u2_power == expected_u2
        sup = max(map(abs, f))
        lower_ratio = u2_power / sup**4
        assert lower_ratio == F(n * (n*n + n + 1), 3 * (n + 1)**3)
        rows.append({
            "n": n, "group_order": N, "energy": energy,
            "U2_fourth_power": str(u2_power), "lower_ratio": str(lower_ratio),
        })
    return rows


def displayed_constants():
    rows = []
    for d in range(4, 11):
        m = 2 ** (d - 2)
        cm = F(comb(2*m, m), 2**m)
        assert cm > 2 ** (m // 2)
        b = 2 / (comb(2*m, m) ** (1 / m))
        rows.append({"d": d, "m": m, "C_m": str(cm), "B_d_approx": b})
    assert rows[0]["C_m"] == "35/8"
    q, s = 2, 15
    sqs = sum(q**i for i in range(s - 1))
    assert sqs == 16383
    assert 8*q*sqs == 262128
    assert 2*(4*q)**s == 2**46
    return {
        "norm_bounds": rows,
        "c4_lower_endpoint_approx": (8 / 111) ** 0.25,
        "c4_upper_endpoint_approx": (8 / 35) ** 0.25,
        "binary_order_eight": {
            "S_qs": sqs, "threshold_coefficient": 8*q*sqs,
            "retention_denominator": 2**46,
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "status": "PASS",
        "arithmetic": "Exact integers/Fraction; decimals are displays only.",
        "scope": "Finite diagnostics; see the written proofs for general theorems.",
        **cube_coefficients(),
        "interval_models": interval_models(),
        **displayed_constants(),
    }
    result["interval_model_count"] = len(result["interval_models"])
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "status": result["status"],
        "balanced_four_cube_subsets": result["balanced_four_cube_subsets"],
        "interval_model_count": result["interval_model_count"],
        "binary_order_eight": result["binary_order_eight"],
    }, indent=2))


if __name__ == "__main__":
    main()
