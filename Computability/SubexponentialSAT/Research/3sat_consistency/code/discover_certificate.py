#!/usr/bin/env python3
"""Optional NumPy discovery of support-consistency potentials.

This floating-point search is NOT part of the trusted mathematical replay.
It holds the supplied finite plans and rational mixing weights fixed. It
runs max-sum diffusion, rounds potentials to a chosen grid, restores their
zero-sum identities exactly, and recomputes every pair maximum in integers.
There is no optimization or global-convergence claim. The shipped main
certificate can be checked without NumPy, SciPy, this script, or a solver.

Run from anywhere, for example:
  python3 code/discover_certificate.py --sweeps 80
The default output is a new results file, never the input certificate.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, permutations
import json
from math import lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRIPLES = sorted(set(permutations((1_400_007, 1_400_007, 0))) |
                 set(permutations((1_400_000, 1_175_014, 750_000))))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def build_supports(r, plan):
    require(len(plan) == 3 and all(plan), "Three nonempty blocks required")
    require(sorted(x for block in plan for x in block) == list(range(r)),
            "Invalid partition")
    operations = []

    def merge(block):
        if len(block) < 2:
            return
        mid = len(block) // 2
        left, right = block[:mid], block[mid:]
        merge(left)
        merge(right)
        operations.append((left, right, sorted(set(range(r)) - set(block))))

    for block in plan:
        merge(block)
    operations.append(plan)
    edges = list(combinations(range(r), 2))
    supports = []
    for parts in operations:
        classes = {v: i for i, block in enumerate(parts) for v in block}
        for triple in TRIPLES:
            weights = dict(zip(((0, 1), (0, 2), (1, 2)), triple))
            supports.append(tuple(0 if classes[x] == classes[y] else
                                  weights[tuple(sorted((classes[x], classes[y])))]
                                  for x, y in edges))
    return supports


def discover(source, sweeps, potential_denominator):
    try:
        import numpy as np
    except ImportError as exc:
        raise SystemExit("Optional discovery needs NumPy; exact certificate replay does not.") from exc
    r, q, scale = source["r"], source["q"], source["support_scale"]
    plans = source["plans"]
    integers = source["mixing_weights"]
    weight_denominator = source["mixing_denominator"]
    require(q == len(plans) and q >= 2, "Invalid plan count")
    require(len(integers) == q and min(integers) >= 0 and
            sum(integers) == weight_denominator > 0, "Invalid rational mixture")
    require(scale == 1_400_000, "Only the documented rectangle supports are implemented")
    require(sweeps >= 0 and potential_denominator > 0, "Invalid search parameters")
    raw = [build_supports(r, plan) for plan in plans]
    require(len(set(map(len, raw))) == 1, "This search expects equally sized menus")
    vectors = np.array(raw, dtype=np.float64) / scale
    mixture = np.array(integers, dtype=np.float64) / weight_denominator
    norms = (vectors * vectors).sum(axis=2)
    pairs = list(combinations(range(q), 2))
    costs = np.array([
        (mixture[i] ** 2 * norms[i, :, None] +
         mixture[j] ** 2 * norms[j, None, :]) / (q - 1) +
        2 * mixture[i] * mixture[j] * (vectors[i] @ vectors[j].T)
        for i, j in pairs
    ])
    potentials = np.zeros((len(pairs), 2, len(raw[0])))
    incident = [[e for e, pair in enumerate(pairs) if i in pair] for i in range(q)]
    initial = float(costs.max(axis=(1, 2)).sum())
    for _ in range(sweeps):
        for i in range(q):
            marginal = np.array([
                (costs[e] + potentials[e, 0, :, None] +
                 potentials[e, 1, None, :]).max(axis=1 if pairs[e][0] == i else 0)
                for e in incident[i]
            ])
            average = marginal.mean(axis=0)
            for e, row in zip(incident[i], marginal):
                endpoint = 0 if pairs[e][0] == i else 1
                potentials[e, endpoint] += average - row
    discovered = float((costs + potentials[:, 0, :, None] +
                        potentials[:, 1, None, :]).max(axis=(1, 2)).sum())

    # Exact feasibility restoration: define the last incident potential as
    # minus the sum of the others, independently for every plan/support.
    rational_potentials = {}
    for i in range(q):
        for e in incident[i][:-1]:
            endpoint = 0 if pairs[e][0] == i else 1
            rational_potentials[f"{e},{i}"] = [
                round(float(x) * potential_denominator) for x in potentials[e, endpoint]
            ]
        last = incident[i][-1]
        rational_potentials[f"{last},{i}"] = [
            -sum(rational_potentials[f"{e},{i}"][k] for e in incident[i][:-1])
            for k in range(len(raw[i]))
        ]
        for k in range(len(raw[i])):
            require(sum(rational_potentials[f"{e},{i}"][k] for e in incident[i]) == 0,
                    "Zero-sum restoration failed")

    # Exact post-search certificate. Floats never accept an inequality here.
    normalizer = (q - 1) * weight_denominator ** 2 * scale ** 2
    common_denominator = lcm(normalizer, potential_denominator)
    cost_multiplier = common_denominator // normalizer
    potential_multiplier = common_denominator // potential_denominator
    integer_norms = [[sum(a * a for a in row) for row in menu] for menu in raw]
    maxima, witnesses = [], []
    for e, (i, j) in enumerate(pairs):
        wi, wj = integers[i], integers[j]
        pi, pj = rational_potentials[f"{e},{i}"], rational_potentials[f"{e},{j}"]
        value, h, k = max(
            ((wi * wi * integer_norms[i][h] + wj * wj * integer_norms[j][k] +
              2 * (q - 1) * wi * wj * sum(a * b for a, b in zip(v, z))) * cost_multiplier +
             (pi[h] + pj[k]) * potential_multiplier, h, k)
            for h, v in enumerate(raw[i]) for k, z in enumerate(raw[j])
        )
        maxima.append(value)
        witnesses.append([h, k])
    u = Fraction(sum(maxima), common_denominator)
    beta_squared = 2 * u / (r * r)
    result = {
        "r": r, "q": q, "support_scale": scale, "plans": plans,
        "mixing_weights": integers, "mixing_denominator": weight_denominator,
        "potential_denominator": potential_denominator,
        "potentials": rational_potentials, "pairs": pairs,
        "beta_squared": str(beta_squared),
        "discovery_only": {
            "algorithm": "Fixed-weight max-sum diffusion; no optimality claim",
            "sweeps": sweeps, "initial_float_U": initial,
            "final_float_U": discovered, "exact_rational_U": str(u),
            "pair_maxima_denominator": common_denominator,
            "pair_maxima": maxima, "witnesses": witnesses,
        },
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=ROOT / "data/support_consistency_certificate.json")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/rediscovered_certificate.json")
    parser.add_argument("--sweeps", type=int, default=80)
    parser.add_argument("--potential-denominator", type=int, default=10 ** 12)
    args = parser.parse_args()
    require(args.output.resolve() != args.certificate.resolve(), "Refusing to overwrite input")
    source = json.loads(args.certificate.read_text())
    result = discover(source, args.sweeps, args.potential_denominator)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "discovery complete; run the independent exact checker",
                      "beta_squared": result["beta_squared"],
                      "float_U_for_display": result["discovery_only"]["final_float_U"],
                      "sweeps": args.sweeps}, indent=2))


if __name__ == "__main__":
    main()
