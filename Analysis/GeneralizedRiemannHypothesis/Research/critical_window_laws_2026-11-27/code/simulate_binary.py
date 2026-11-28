#!/usr/bin/env python3
"""Reproducible illustrations, not proofs, of the two critical-window laws.

Uses only the Python standard library.  All finite-field operations are exact
over F_2.  Run from the archive root, optionally with --trials 5000.
"""
import argparse
import json
import math
import random
from collections import Counter
from functools import lru_cache
from pathlib import Path


def row_echelon(rows):
    pivots = {}
    for row in rows:
        while row:
            p = row.bit_length() - 1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
    return pivots


def kernel_basis(pivots, width):
    ans = []
    for free in range(width):
        if free in pivots:
            continue
        v = 1 << free
        for p in sorted(pivots):
            if (pivots[p] & v).bit_count() % 2:
                v ^= 1 << p
        ans.append(v)
    return ans


def features_square(n):
    pairs = [(i, j) for i in range(n) for j in range(i, n)]

    @lru_cache(maxsize=100000)
    def encode(x):
        return sum(((x >> i) & (x >> j) & 1) << b
                   for b, (i, j) in enumerate(pairs))
    return encode, len(pairs)


def features_plane(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]

    def encode(x, y):
        return sum(((((x >> i) & (y >> j)) ^
                      ((x >> j) & (y >> i))) & 1) << b
                   for b, (i, j) in enumerate(pairs))
    return encode, pairs


def alternating_rank(code, n, pairs):
    rows = [0] * n
    for bit, (i, j) in enumerate(pairs):
        if (code >> bit) & 1:
            rows[i] |= 1 << j
            rows[j] |= 1 << i
    return len(row_echelon(rows))


def nonsingular_count(basis, n, pairs):
    span = [0]
    for v in basis:
        span += [x ^ v for x in span]
    return sum(alternating_rank(x, n, pairs) == n for x in span[1:])


def gamma(j):
    return math.prod(1 - 2.0 ** (-i) for i in range(1, j + 1))


def pi(u, k):
    if k < max(0, -u):
        return 0.0
    return gamma(100) * 2.0 ** (-k * (k + u)) / (gamma(k) * gamma(k + u))


def summary(values):
    n = len(values)
    avg = sum(values) / n
    var = sum((x - avg) ** 2 for x in values) / max(n - 1, 1)
    return {"estimate": avg, "standard_error": math.sqrt(var / n)}


def square_experiment(rng, n, u, trials):
    encode, d = features_square(n)
    counts = Counter()
    for _ in range(trials):
        cols = [rng.getrandbits(n) for _ in range(d + u)]
        # Conditioning on full generator rank produces a uniform [N,n] code.
        while len(row_echelon(cols)) < n:
            cols = [rng.getrandbits(n) for _ in range(d + u)]
        rank = len(row_echelon(encode(x) for x in cols))
        counts[d - rank] += 1
    maxk = max(max(counts), 7)
    empirical = {str(k): counts[k] / trials for k in range(maxk + 1)}
    limiting = {str(k): pi(u, k) for k in range(maxk + 1)}
    tv = .5 * (sum(abs(empirical[str(k)] - limiting[str(k)])
                     for k in range(maxk + 1))
                + max(0.0, 1 - sum(limiting.values())))
    return {"model": "uniform_binary_code_square", "generator_dimension": n,
            "length": d + u, "offset": u, "trials": trials,
            "nullity_frequencies": dict(sorted(counts.items())),
            "empirical_probabilities": empirical, "limit_probabilities": limiting,
            "empirical_TV_to_limit": tv,
            "full_rank_probability": summary([1] * counts[max(0, -u)] +
                                              [0] * (trials-counts[max(0, -u)])),
            "full_rank_limit": gamma(100) / gamma(abs(u))}


def hidden_experiment(rng, n, a, trials):
    encode, pairs = features_plane(n)
    d = len(pairs)
    t = d - 1 + a
    c_n = math.prod(1 - 2.0 ** (-(2*j-1)) for j in range(2, n//2+1))
    p_n = (2**(n-2)-1)/(2**(n-1)-1)
    mu_n = 2.0**(d-1) * c_n * p_n**t
    stats = {name: [] for name in ["likelihood_mean", "TV", "optimal_recovery",
                                  "unique_candidate", "elimination_recovery"]}
    counts = Counter()
    for _ in range(trials):
        rows = []
        for _ in range(t):
            x = rng.randrange(1, 1 << n)
            y = rng.randrange(1, 1 << n)
            while y == x:
                y = rng.randrange(1, 1 << n)
            rows.append(encode(x, y))
        basis = kernel_basis(row_echelon(rows), d)
        assert all((row & v).bit_count() % 2 == 0 for row in rows for v in basis)
        z = nonsingular_count(basis, n, pairs)
        counts[(len(basis), z)] += 1
        likelihood = z / mu_n
        stats["likelihood_mean"].append(likelihood)
        stats["TV"].append(abs(likelihood-1)/2)
        stats["optimal_recovery"].append((z > 0)/mu_n)
        stats["unique_candidate"].append((z == 1)/mu_n)
        stats["elimination_recovery"].append((len(basis) == 1 and z == 1)/mu_n)
    return {"model": "hidden_alternating_null_samples", "ambient_dimension": n,
            "offset_from_projective_dimension": a, "sample_count": t,
            "trials": trials, "exact_finite_mean_Z": mu_n,
            "estimates": {k: summary(v) for k, v in stats.items()},
            "joint_counts": [{"kernel_dimension": k, "nonsingular_points": z,
                              "count": v} for (k,z),v in sorted(counts.items())]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=20261127)
    ap.add_argument("--output", default="results/binary_simulations.json")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    out = {"seed": args.seed, "purpose": "Numerical illustration; not proof or finite-size certification",
           "squares": [], "hidden": []}
    for n in (6, 10, 16):
        for u in (-2, 0, 2):
            result = square_experiment(rng, n, u, args.trials)
            out["squares"].append(result)
            print(f"square n={n} u={u}: TV={result['empirical_TV_to_limit']:.5f}", flush=True)
    for n in (6, 10, 14):
        for a in (-1, 0, 1):
            result = hidden_experiment(rng, n, a, args.trials)
            out["hidden"].append(result)
            print(f"hidden n={n} a={a}: TV={result['estimates']['TV']['estimate']:.5f}", flush=True)
    dest = Path(args.output)
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(out, indent=2) + "\n")


if __name__ == "__main__":
    main()
