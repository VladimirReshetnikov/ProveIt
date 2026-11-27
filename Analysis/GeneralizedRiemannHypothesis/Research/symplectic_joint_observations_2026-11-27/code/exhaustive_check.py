#!/usr/bin/env python3
"""Independent exhaustive checks for the joint law of prescribed-Gram frames.

Only prime fields are used.  All counts and probabilities are exact integers
and fractions.  The empirical side enumerates actual ordered frames with fixed Gram;
the predicted side uses Gaussian coefficients and radical inclusion-exclusion.
No simulation, floating-point linear algebra, or external package is involved.

Run from any directory:
    python3 exhaustive_check.py
    python3 exhaustive_check.py --quick
Results are written next to the code under ../results/.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod
from pathlib import Path
import json
import time


def rank_mod(rows, q):
    """Row rank by Gaussian elimination over the prime field F_q."""
    if not rows:
        return 0
    a = [[x % q for x in row] for row in rows]
    ncols = len(a[0])
    row = 0
    for col in range(ncols):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inv = pow(a[row][col], -1, q)
        a[row] = [(x * inv) % q for x in a[row]]
        for i in range(row + 1, len(a)):
            if a[i][col]:
                c = a[i][col]
                a[i] = [(u - c * v) % q for u, v in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def symplectic(v, w, q):
    n = len(v) // 2
    return sum(v[i] * w[n + i] - v[n + i] * w[i]
               for i in range(n)) % q


def canonical_gram(q, d, s):
    matrix = [[0] * d for _ in range(d)]
    for i in range(s):
        matrix[2 * i][2 * i + 1] = 1
        matrix[2 * i + 1][2 * i] = -1 % q
    return matrix


@lru_cache(None)
def prescribed_gram_frames(q, n, d, s=0):
    """Enumerate ordered independent d-tuples with a canonical rank-2s Gram."""
    if not 0 <= 2 * s <= d or n - d + s < 0:
        return ()
    target = canonical_gram(q, d, s)
    vectors = list(product(range(q), repeat=2 * n))
    frames = [()]
    for _ in range(d):
        following = []
        for frame in frames:
            for v in vectors:
                if not any(v):
                    continue
                if any(symplectic(w, v, q) != target[i][len(frame)]
                       for i, w in enumerate(frame)):
                    continue
                if rank_mod(frame + (v,), q) == len(frame) + 1:
                    following.append(frame + (v,))
        frames = following
    return tuple(frames)


@lru_cache(None)
def gaussian(q, n, k):
    if k < 0 or n < 0 or k > n:
        return 0
    k = min(k, n - k)
    numerator = prod(q ** (n - j) - 1 for j in range(k))
    denominator = prod(q ** (k - j) - 1 for j in range(k))
    assert numerator % denominator == 0
    return numerator // denominator


@lru_cache(None)
def eta(q, n):
    if n < 0:
        raise ValueError("eta index must be nonnegative")
    return prod((Fraction(q ** (2 * h) - 1, q ** (2 * h))
                 for h in range(1, n + 1)), start=Fraction(1))


def qpower(q, exponent):
    return (Fraction(q ** exponent) if exponent >= 0
            else Fraction(1, q ** (-exponent)))


@lru_cache(None)
def embeddings(q, n, a, s):
    """Injective isometries of an a-space of alternating rank 2s."""
    if a < 0 or s < 0 or 2 * s > a or n - a + s < 0:
        return 0
    answer = qpower(q, 2 * n * a - a * (a - 1) // 2)
    answer *= eta(q, n) / eta(q, n - a + s)
    assert answer.denominator == 1
    return answer.numerator


@lru_cache(None)
def kernel_count(q, radical_dim, intersection_dims, ell):
    """Number of ell-subspaces of R avoiding each R cap E_i."""
    total = 0
    for js in product(*(range(t + 1) for t in intersection_dims)):
        j = sum(js)
        total += ((-1) ** j
                  * q ** sum(x * (x - 1) // 2 for x in js)
                  * prod(gaussian(q, t, x)
                         for t, x in zip(intersection_dims, js))
                  * gaussian(q, radical_dim - j, ell - j))
    assert total >= 0
    return total


def block_gram(output, dims, q, half_ranks=None):
    half_ranks = half_ranks or (0,) * len(dims)
    d = sum(dims)
    matrix = [[0] * d for _ in range(d)]
    starts = [sum(dims[:i]) for i in range(len(dims))]
    for block, (width, s) in enumerate(zip(dims, half_ranks)):
        diagonal = canonical_gram(q, width, s)
        for i in range(width):
            for j in range(width):
                matrix[starts[block] + i][starts[block] + j] = diagonal[i][j]
    cursor = 0
    for i in range(len(dims)):
        for j in range(i + 1, len(dims)):
            for u in range(dims[i]):
                for v in range(dims[j]):
                    x, y = starts[i] + u, starts[j] + v
                    matrix[x][y] = output[cursor]
                    matrix[y][x] = -output[cursor] % q
                    cursor += 1
    assert cursor == len(output)
    return matrix


def gram_parameters(matrix, dims, q):
    d = sum(dims)
    rank = rank_mod(matrix, q)
    assert rank % 2 == 0
    intersections = []
    start = 0
    for width in dims:
        columns = [row[start:start + width] for row in matrix]
        intersections.append(width - rank_mod(columns, q))
        start += width
    return rank // 2, d - rank, tuple(intersections)


@lru_cache(None)
def predicted_count(q, n, dims, s, radical_dim, intersections):
    d = sum(dims)
    return sum(kernel_count(q, radical_dim, intersections, ell)
               * embeddings(q, n, d - ell, s)
               for ell in range(radical_dim + 1))


def observed_histogram(q, n, dims, half_ranks):
    families = [prescribed_gram_frames(q, n, d, s)
                for d, s in zip(dims, half_ranks)]
    # Precompute cross-Gram blocks without using the claimed formula.
    pair_tables = {}
    for i in range(len(dims)):
        for j in range(i + 1, len(dims)):
            pair_tables[i, j] = [
                [tuple(symplectic(v, w, q) for v in left for w in right)
                 for right in families[j]]
                for left in families[i]
            ]
    histogram = Counter()
    for indices in product(*(range(len(family)) for family in families)):
        key = tuple(value for (i, j), table in pair_tables.items()
                    for value in table[indices[i]][indices[j]])
        histogram[key] += 1
    return histogram, [len(family) for family in families]


def uniform_radical_moment(q, dims, half_ranks=None):
    half_ranks = half_ranks or (0,) * len(dims)
    d = sum(dims)
    singleton_support = sum(q ** width - 1 for width in dims)
    return (Fraction(1)
            + sum((q ** (width - 2 * s) - 1) * qpower(q, -(d - width))
                  for width, s in zip(dims, half_ranks))
            + (q ** d - 1 - singleton_support) * qpower(q, -(d - 1)))


def fraction_json(value):
    value = Fraction(value)
    return {"numerator": value.numerator, "denominator": value.denominator,
            "exact": str(value), "decimal": float(value)}


def forest_independence_checks(histogram, dims, denominator):
    """Verify every forest marginal against the product of its edge marginals."""
    edges = []
    cursor = 0
    for i in range(len(dims)):
        for j in range(i + 1, len(dims)):
            width = dims[i] * dims[j]
            edges.append((i, j, cursor, cursor + width))
            cursor += width
    marginals = []
    for _, _, begin, end in edges:
        marginal = Counter()
        for output, count in histogram.items():
            marginal[output[begin:end]] += count
        marginals.append(marginal)
    checked = 0
    for mask in range(1 << len(edges)):
        selected = [i for i in range(len(edges)) if mask & (1 << i)]
        if len(selected) < 2:
            continue
        parent = list(range(len(dims)))
        def find(x):
            while x != parent[x]:
                x = parent[x]
            return x
        is_forest = True
        for index in selected:
            i, j, _, _ = edges[index]
            i, j = find(i), find(j)
            if i == j:
                is_forest = False
                break
            parent[i] = j
        if not is_forest:
            continue
        joint = Counter()
        for output, count in histogram.items():
            key = tuple(output[edges[index][2]:edges[index][3]] for index in selected)
            joint[key] += count
        for key in product(*(tuple(marginals[index]) for index in selected)):
            numerator = prod(marginals[index][value]
                             for index, value in zip(selected, key))
            assert joint[key] * denominator ** (len(selected) - 1) == numerator
        checked += 1
    return checked


def run_case(q, n, dims, half_ranks=None):
    started = time.perf_counter()
    dims = tuple(dims)
    half_ranks = tuple(half_ranks or (0,) * len(dims))
    assert len(dims) == len(half_ranks) >= 2
    assert all(1 <= d and 0 <= 2 * s <= d and n - d + s >= 0
               for d, s in zip(dims, half_ranks))
    observed, family_sizes = observed_histogram(q, n, dims, half_ranks)
    denominator = prod(family_sizes)
    expected_denominator = prod(embeddings(q, n, d, s)
                                for d, s in zip(dims, half_ranks))
    assert denominator == expected_denominator
    assert sum(observed.values()) == denominator
    d = sum(dims)
    b = sum(dims[i] * dims[j] for i in range(len(dims))
            for j in range(i + 1, len(dims)))
    uniform_probability = Fraction(1, q ** b)
    total_variation = Fraction(0)
    uniform_moment = Fraction(0)
    impossible_rank_mass = Fraction(0)
    pointwise = []
    invariants = Counter()
    for output in product(range(q), repeat=b):
        matrix = block_gram(output, dims, q, half_ranks)
        s, radical_dim, intersections = gram_parameters(matrix, dims, q)
        count = predicted_count(q, n, dims, s, radical_dim, intersections)
        actual = observed[output]
        assert count == actual, (q, n, dims, output, count, actual)
        assert (actual > 0) == (s + max(intersections) <= n)
        probability = Fraction(count, denominator)
        total_variation += abs(probability - uniform_probability) / 2
        uniform_moment += q ** radical_dim * uniform_probability
        if s > n:
            impossible_rank_mass += uniform_probability
            assert actual == 0
        invariants[(s, radical_dim, intersections, count)] += 1
        pointwise.append({"cross_gram_entries": list(output),
                          "rank": 2 * s, "nullity": radical_dim,
                          "block_radical_intersections": list(intersections),
                          "observed_count": actual, "formula_count": count})
    assert uniform_moment == uniform_radical_moment(q, dims, half_ranks)
    assert impossible_rank_mass <= total_variation <= 1
    balanced = all(2 * width <= d for width in dims)
    if balanced:
        assert uniform_moment <= q + 1 + len(dims)
    if d <= 2 * n:
        theorem_bound = min(Fraction(1), uniform_moment / (q * q - 1)
                            * qpower(q, -(2 * n - d)))
        assert total_variation <= theorem_bound
        bound_kind = "subcritical_upper"
    else:
        theorem_bound = max(Fraction(0), 1 - (uniform_moment - 1)
                            / (q ** (d - 2 * n) - 1))
        assert total_variation >= theorem_bound
        bound_kind = "supercritical_lower"
    forest_count = forest_independence_checks(observed, dims, denominator)
    return {
        "q": q, "ambient_half_dimension": n, "block_dimensions": list(dims),
        "individual_gram_ranks": [2 * s for s in half_ranks],
        "combined_dimension": d, "cross_block_entries": b,
        "individual_frame_counts": family_sizes,
        "frame_tuples_enumerated": denominator,
        "gram_matrices_checked": q ** b,
        "positive_probability_gram_matrices": len(observed),
        "pointwise_formula_matches": True,
        "exact_total_variation": fraction_json(total_variation),
        "uniform_mean_q_to_nullity": fraction_json(uniform_moment),
        "uniform_rank_above_ambient_probability": fraction_json(impossible_rank_mass),
        "support_lower_bound_checked": True,
        "exact_support_criterion_checked": True,
        "balanced_blocks": balanced,
        "balanced_moment_bound_checked": balanced,
        "theorem_tv_bound_kind": bound_kind,
        "theorem_tv_bound": fraction_json(theorem_bound),
        "theorem_tv_bound_checked": True,
        "forest_marginals_checked": forest_count,
        "forest_independence_checked": True,
        "invariant_classes": [
            {"rank": 2 * key[0], "nullity": key[1],
             "block_radical_intersections": list(key[2]),
             "probability_numerator_count": key[3], "number_of_gram_matrices": value}
            for key, value in sorted(invariants.items())
        ],
        "pointwise_counts": pointwise,
        "elapsed_seconds": round(time.perf_counter() - started, 6),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="run first four cases only")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "exhaustive_checks.json")
    args = parser.parse_args()
    cases = [(2, 1, (1, 1, 1), None), (2, 1, (1, 1, 1, 1), None),
             (3, 1, (1, 1, 1), None), (2, 2, (2, 1, 1), None),
             (2, 2, (1, 1, 1, 1), None), (2, 2, (2, 2, 1), None),
             (3, 2, (1, 1, 1), None), (2, 2, (2, 1, 1), (1, 0, 0)),
             (3, 1, (2, 1, 1), (1, 0, 0))]
    if args.quick:
        cases = cases[:4]
    results = []
    for q, n, dims, half_ranks in cases:
        result = run_case(q, n, dims, half_ranks)
        results.append(result)
        print(f"q={q}, n={n}, blocks={dims}, ranks={result['individual_gram_ranks']}: "
              f"{result['frame_tuples_enumerated']} frame tuples, "
              f"{result['gram_matrices_checked']} Gram matrices, "
              f"TV={result['exact_total_variation']['exact']}; PASS", flush=True)
    summary = {
        "description": "Exhaustive independent enumeration of joint prescribed-Gram frame laws",
        "arithmetic": "Python standard library; exact prime-field and rational arithmetic",
        "all_checks_passed": True,
        "number_of_cases": len(results),
        "total_frame_tuples_enumerated": sum(r["frame_tuples_enumerated"] for r in results),
        "total_gram_matrices_checked": sum(r["gram_matrices_checked"] for r in results),
        "cases": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Saved {args.output}", flush=True)


if __name__ == "__main__":
    main()
