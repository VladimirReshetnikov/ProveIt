#!/usr/bin/env python3
"""Exact, reproducible recovery examples over prime fields; Python stdlib only.

Run from the package root: python3 code/recovery_demo.py
All random choices use fixed, recorded seeds. This is a finite illustration,
not a proof of the asymptotic threshold.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, int(p**0.5) + 1))


def rref(rows: list[list[int]], p: int, ncols: int):
    a = [[x % p for x in row] for row in rows]
    assert all(len(row) == ncols for row in a)
    pivots = []
    k = 0
    for j in range(ncols):
        pivot = next((i for i in range(k, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[k], a[pivot] = a[pivot], a[k]
        scale = pow(a[k][j], -1, p)
        a[k] = [(scale * x) % p for x in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                c = a[i][j]
                a[i] = [(x - c * y) % p for x, y in zip(a[i], a[k])]
        pivots.append(j)
        k += 1
        if k == len(a):
            break
    return a[:k], pivots


def nullspace(rows: list[list[int]], p: int, ncols: int):
    a, pivots = rref(rows, p, ncols)
    free = [j for j in range(ncols) if j not in pivots]
    result = []
    for f in free:
        x = [0] * ncols
        x[f] = 1
        for i, j in enumerate(pivots):
            x[j] = -a[i][f] % p
        result.append(x)
    return result


def dot(x, y, p):
    return sum(a * b for a, b in zip(x, y)) % p


def normalize(v, p):
    j = next(i for i, x in enumerate(v) if x % p)
    a = pow(v[j] % p, -1, p)
    return [a * x % p for x in v]


def random_form(n, p, rng):
    while True:
        s = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
        if len(rref(s, p, n)[1]) == n:
            break
    # H = S^T J S, with J the block diagonal standard alternating form.
    h = [[sum(s[2*k][i]*s[2*k+1][j] - s[2*k+1][i]*s[2*k][j]
              for k in range(n//2)) % p
          for j in range(n)] for i in range(n)]
    assert len(rref(h, p, n)[1]) == n
    assert all(h[i][i] == 0 for i in range(n))
    assert all((h[i][j]+h[j][i]) % p == 0 for i in range(n) for j in range(n))
    return h


def isotropic_plane(h, p, rng):
    n = len(h)
    while True:
        u = [rng.randrange(p) for _ in range(n)]
        if any(u):
            break
    linear = [sum(u[i] * h[i][j] for i in range(n)) % p for j in range(n)]
    while True:
        v = [rng.randrange(p) for _ in range(n)]
        if dot(linear, v, p) == 0 and len(rref([u, v], p, n)[1]) == 2:
            # Every isotropic plane has the same number of independent bases.
            plane, _ = rref([u, v], p, n)
            return plane


def coefficient_row(plane, p):
    u, v = plane
    return [(u[i]*v[j] - u[j]*v[i]) % p
            for i in range(len(u)) for j in range(i+1, len(u))]


def run_example(n, p, seed, excess=12):
    assert is_prime(p), "This implementation supports prime fields only."
    assert n >= 4 and n % 2 == 0
    rng = random.Random(seed)
    h = random_form(n, p, rng)
    hvector = [h[i][j] for i in range(n) for j in range(i+1, n)]
    dimension = n*(n-1)//2
    threshold = dimension-1
    rows, planes, ranks = [], [], []
    first_recovery = None
    for sample in range(1, threshold+excess+1):
        plane = isotropic_plane(h, p, rng)
        row = coefficient_row(plane, p)
        assert any(row)
        assert dot(row, hvector, p) == 0
        planes.append(plane)
        rows.append(row)
        rank = len(rref(rows, p, dimension)[1])
        ranks.append(rank)
        if rank == threshold and first_recovery is None:
            first_recovery = sample
    solutions = nullspace(rows, p, dimension)
    recovered = len(solutions) == 1 and normalize(solutions[0], p) == normalize(hvector, p)
    if not recovered:
        raise AssertionError(f"Recorded example failed recovery: n={n}, q={p}, seed={seed}")
    return {
        "field_order": p, "dimension": n, "seed": seed,
        "coefficient_dimension_D": dimension, "threshold_d": threshold,
        "samples": len(planes), "first_linear_recovery_at": first_recovery,
        "final_constraint_rank": ranks[-1], "solution_dimension": len(solutions),
        "recovered_projective_form_matches": recovered,
        "true_form_upper_triangle": normalize(hvector, p),
        "recovered_upper_triangle": normalize(solutions[0], p),
        "prefix_constraint_ranks": ranks, "sampled_plane_rref_bases": planes,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "data" / "recovery_demo.json")
    args = parser.parse_args()
    specifications = [(6, 2, 260627), (8, 2, 280827), (12, 2, 2121227),
                      (8, 3, 380827)]
    examples = [run_example(n, p, seed) for n, p, seed in specifications]
    result = {
        "purpose": "Exact fixed-seed illustrations, not an asymptotic statistical test",
        "arithmetic": "Prime-field arithmetic using Python integers; no floating point",
        "all_examples_passed": all(x["recovered_projective_form_matches"] for x in examples),
        "examples": examples,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"all_examples_passed": result["all_examples_passed"],
                      "examples": [{k: x[k] for k in
                                    ("field_order", "dimension", "threshold_d", "samples",
                                     "first_linear_recovery_at", "final_constraint_rank")}
                                   for x in examples]}, indent=2))


if __name__ == "__main__":
    main()
