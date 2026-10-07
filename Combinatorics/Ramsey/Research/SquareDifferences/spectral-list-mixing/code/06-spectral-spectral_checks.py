#!/usr/bin/env python3
"""Reproducible checks for the spectral replacement and marking estimates.

Exact rational checks are labeled separately from floating-point diagnostics.
The script is supporting evidence; the manuscript supplies the proofs.
Requires Python 3 and NumPy. From the spectral_transfer directory run:
python3 code/spectral_checks.py --output data/spectral_validation.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import permutations, product
import json
import math
from pathlib import Path
import platform

import numpy as np


SEED = 20261007159
TOL = 2e-10


def spectral_norm(kernel, row_weights=None, column_weights=None):
    nr, nc = kernel.shape
    if row_weights is None:
        row_weights = np.full(nr, 1.0 / nr)
    if column_weights is None:
        column_weights = np.full(nc, 1.0 / nc)
    weighted = np.sqrt(row_weights)[:, None] * kernel
    weighted *= np.sqrt(column_weights)[None, :]
    return float(np.linalg.svd(weighted, compute_uv=False)[0])


def prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def exact_square_norm(p):
    if p % 4 == 1:
        return (math.sqrt(p) + 1) / (2 * p)
    return math.sqrt(p + 1) / (2 * p)


def square_matrix(p):
    residues = {x * x % p for x in range(1, p)}
    return np.array([[int((y - x) % p in residues)
                      for y in range(p)] for x in range(p)], dtype=float)


def square_fourier_checks():
    errors = []
    rows = []
    for p in range(3, 102, 2):
        if not prime(p):
            continue
        matrix = square_matrix(p)
        expected = exact_square_norm(p)
        fft_norm = float(np.max(np.abs(np.fft.fft(matrix[0] - 0.5))) / p)
        svd_norm = spectral_norm(matrix - 0.5)
        errors += [abs(fft_norm - expected), abs(svd_norm - expected)]
        assert max(errors[-2:]) < TOL
        rows.append({"p": p, "formula": expected,
                     "fft": fft_norm, "svd": svd_norm})
    return {"kind": "floating_point_diagnostic", "prime_count": len(rows),
            "maximum_absolute_error": max(errors), "values": rows}


def all_oriented_patterns():
    positions = list(product(range(2), repeat=2))
    checked = 0
    ratios = []
    worst_residual = -1.0
    for p in (3, 5, 7):
        matrix = square_matrix(p)
        words = np.array(list(product(range(p), repeat=2)))
        for states in product((0, 1, -1), repeat=4):
            kernel = np.ones((p * p, p * p))
            m = sum(state != 0 for state in states)
            for (i, j), state in zip(positions, states):
                if state:
                    base = matrix if state == 1 else matrix.T
                    kernel *= base[words[:, i, None], words[None, :, j]]
            actual = spectral_norm(kernel - 2.0 ** (-m))
            bound = 2 * (1 - 2.0 ** (-m)) * exact_square_norm(p)
            worst_residual = max(worst_residual, actual - bound)
            assert actual <= bound + TOL
            if bound:
                ratios.append(actual / bound)
            checked += 1
    return {"kind": "floating_point_diagnostic", "primes": [3, 5, 7],
            "patterns_per_prime": 81, "total_checks": checked,
            "maximum_norm_over_bound": max(ratios),
            "maximum_signed_bound_residual": worst_residual}


def product_space(dimensions, rng):
    words = np.array(list(product(*(range(n) for n in dimensions))))
    weights = []
    for n in dimensions:
        w = rng.integers(1, 10, size=n).astype(float)
        weights.append(w / np.sum(w))
    full_weights = np.ones(len(words))
    for i, w in enumerate(weights):
        full_weights *= w[words[:, i]]
    return words, weights, full_weights


def ordered_bound(order, densities, errors):
    prefix, result = 1, 0
    for i in order:
        result += prefix * errors[i]
        prefix *= densities[i]
    return result


def heterogeneous_checks(rng):
    left_dims, right_dims = (2, 3, 2), (3, 2, 2)
    universe = list(product(range(3), repeat=2))
    checks, orders_checked, worst_ratio = 0, 0, 0.0
    for m in range(1, 8):
        for _ in range(4):
            left, lw, lp = product_space(left_dims, rng)
            right, rw, rp = product_space(right_dims, rng)
            indices = rng.choice(len(universe), size=m, replace=False)
            edges = [universe[int(i)] for i in indices]
            densities = rng.integers(0, 10, size=m).astype(float) / 10
            errors = []
            kernel = np.ones((len(left), len(right)))
            for e, (i, j) in enumerate(edges):
                base = rng.random((left_dims[i], right_dims[j]))
                errors.append(spectral_norm(base - densities[e], lw[i], rw[j]))
                kernel *= base[left[:, i, None], right[None, :, j]]
            sorted_order = tuple(sorted(range(m),
                                        key=lambda i: errors[i] / (1 - densities[i])))
            bound = ordered_bound(sorted_order, densities, errors)
            minimum = min(ordered_bound(order, densities, errors)
                          for order in permutations(range(m)))
            orders_checked += math.factorial(m)
            assert abs(bound - minimum) < TOL
            actual = spectral_norm(kernel - np.prod(densities), lp, rp)
            assert actual <= bound + TOL
            worst_ratio = max(worst_ratio, actual / bound)
            checks += 1
    return {"kind": "floating_point_diagnostic", "nonuniform_cases": checks,
            "all_replacement_orders_checked": orders_checked,
            "maximum_edges": 7, "maximum_norm_over_best_bound": worst_ratio}


def exact_order_checks(rng):
    checks, order_count = 0, 0
    for m in range(1, 8):
        densities = [Q(int(rng.integers(0, 10)), 10) for _ in range(m)]
        errors = [Q(int(rng.integers(1, 21)), 23) for _ in range(m)]
        best = tuple(sorted(range(m), key=lambda i: errors[i] / (1 - densities[i])))
        predicted = ordered_bound(best, densities, errors)
        actual = min(ordered_bound(order, densities, errors)
                     for order in permutations(range(m)))
        assert predicted == actual
        order_count += math.factorial(m)
        checks += 1
    return {"kind": "exact_rational", "cases": checks,
            "all_orders_checked": order_count, "all_equal": True}


def exact_telescoping_checks(rng):
    possible_edges = list(product(range(3), repeat=2))
    checked = 0
    for m in range(8):
        edges = possible_edges[:m]
        kernels = [[[Q(int(rng.integers(0, 8)), 7) for _ in range(2)]
                    for _ in range(2)] for _ in edges]
        densities = [Q(int(rng.integers(0, 11)), 10) for _ in edges]
        orders = [tuple(range(m)), tuple(reversed(range(m)))]
        for bits in product(range(2), repeat=6):
            values = [kernels[e][bits[i]][bits[3 + j]]
                      for e, (i, j) in enumerate(edges)]
            lhs = math.prod(values) - math.prod(densities)
            for order in orders:
                rhs = sum((math.prod(densities[order[s]] for s in range(r))
                           * (values[order[r]] - densities[order[r]])
                           * math.prod(values[order[s]] for s in range(r + 1, m))
                           for r in range(m)), Q(0))
                assert lhs == rhs
                checked += 1
    return {"kind": "exact_rational", "pointwise_identities_checked": checked,
            "empty_product_included": True, "all_equal": True}


def marked_interaction_checks():
    results = []
    for h in (3, 4, 5):
        words = [w for w in permutations(range(h)) if w.index(0) < w.index(1)]
        delta = Q(1, 10 * h * h)
        kappa = Q(9, 10) * delta ** (h - 1)

        def theta(w):
            return tuple(1 if z == 0 else 0 if z == 1 else z for z in w)

        def interaction(x, z):
            changed = [i for i in range(h) if x[i] != z[i]]
            if len(changed) != 2:
                return Q(0)
            i, j = changed
            if x[i] == z[j] and x[j] == z[i]:
                return delta ** (j - i)
            return Q(0)

        matrix = [[interaction(x, theta(y)) for y in words] for x in words]
        gaps, ratios = [], []
        for i in range(len(words)):
            assert all(matrix[i][j] == matrix[j][i] for j in range(len(words)))
            diagonal = matrix[i][i]
            off_diagonal = sum(matrix[i], Q(0)) - diagonal
            assert off_diagonal <= diagonal / 10
            assert diagonal - off_diagonal >= kappa
            gaps.append(diagonal - off_diagonal)
            ratios.append(off_diagonal / diagonal)
        results.append({"h": h, "matrix_order": len(words),
                        "kappa": str(kappa), "minimum_diagonal_dominance": str(min(gaps)),
                        "maximum_off_diagonal_over_diagonal": str(max(ratios)),
                        "symmetric": True, "all_row_inequalities_hold": True})
    return {"kind": "exact_rational", "results": results,
            "interpretation": "Diagonal dominance proves A >= kappa I; no floating eigensolver."}


def parallel_edge_warning():
    p = 101
    actual = spectral_norm(square_matrix(p) - 0.25)
    invalid_simple_graph_bound = 1.5 * exact_square_norm(p)
    assert actual > invalid_simple_graph_bound
    return {"kind": "floating_point_diagnostic_with_exact_identity",
            "prime": p, "identity": "A(x,y)^2 = A(x,y)",
            "actual_repeated_edge_norm": actual,
            "invalid_bound_if_simplicity_were_dropped": invalid_simple_graph_bound,
            "conclusion": "The no-parallel-edge hypothesis is necessary."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "spectral_validation.json")
    args = parser.parse_args()
    rng = np.random.default_rng(SEED)
    result = {"seed": SEED, "python": platform.python_version(),
              "numpy": np.__version__, "floating_absolute_tolerance": TOL,
              "status": "all checks passed",
              "scope": "Supporting validation; exact and numerical checks are distinguished.",
              "square_fourier": square_fourier_checks(),
              "oriented_patterns": all_oriented_patterns(),
              "heterogeneous_nonuniform": heterogeneous_checks(rng),
              "replacement_order_exact": exact_order_checks(rng),
              "telescoping_exact": exact_telescoping_checks(rng),
              "marked_interaction_exact": marked_interaction_checks(),
              "parallel_edge_counterexample": parallel_edge_warning()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "square_fourier"}, indent=2))
    print("Full output:", args.output.resolve())


if __name__ == "__main__":
    main()
