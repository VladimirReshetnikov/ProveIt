#!/usr/bin/env python3
"""Independently audit selected quadratic monomial isolation.

Uses only the Python standard library. No imported construction helper or
search implementation is executed. Monomials are sorted tuples of variable
indices, independently of the exponent-vector representation in the builder.

Usage: python3 check_support_independent.py PACKAGE_DIRECTORY
"""
import collections
import hashlib
import itertools
import json
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def plus(a, b, multiplier=1):
    result = collections.Counter(a)
    for monomial, value in b.items():
        result[monomial] += multiplier * value
    return {m: v for m, v in result.items() if v}


def times(a, b):
    result = collections.Counter()
    for m, v in a.items():
        for k, u in b.items():
            result[tuple(sorted(m + k))] += v * u
    return {m: v for m, v in result.items() if v}


def audit(directory):
    data = Path(directory) / "data"
    parent_file = data / "parent_system.json"
    weights_file = data / "weights.json"
    parent = json.loads(parent_file.read_text())
    weights_record = json.loads(weights_file.read_text())
    weights = weights_record["weights_in_parent_coordinate_order"]
    n = len(parent["variables"])
    names = parent["variables"] + parent["constants"]
    require(n == 31, "unexpected parent variable count")
    require(len(weights) == n + 1, "weight count")
    require(weights[0] == 0 and min(weights[1:]) > 0, "weight signs")
    require(len(set(weights)) == len(weights), "duplicate individual weights")
    env = {name: {(i + 1,): 1} for i, name in enumerate(names)}

    def read(value):
        if isinstance(value, int):
            return {(): value} if value else {}
        return env[value]

    for name, op, u, v in parent["source"]:
        require(name not in env, "overwritten arithmetic register")
        require(op in ("+", "-", "*"), "unsupported operation")
        u, v = read(u), read(v)
        env[name] = times(u, v) if op == "*" else plus(u, v, -1 if op == "-" else 1)

    rows = []
    for u, v in parent["comparisons"]:
        shifted = collections.Counter()
        for monomial, coefficient in plus(read(u), read(v), -1).items():
            witness_factors = [i for i in monomial if i <= n]
            port_factors = tuple(i for i in monomial if i > n)
            require(len(witness_factors) <= 2, "nonquadratic parent row")
            for choice in itertools.product((0, 1), repeat=len(witness_factors)):
                key = tuple(i for i, keep in zip(witness_factors, choice) if keep) + port_factors
                shifted[key] += coefficient
        rows.append({m: c for m, c in shifted.items() if c})
    require(len(rows) == 22, "parent row count")

    all_pairs = list(itertools.combinations_with_replacement(range(n + 1), 2))
    sum_fibers = {}
    for pair in all_pairs:
        sum_fibers.setdefault(sum(weights[i] for i in pair), []).append(pair)
    protected = set()
    row_supports = []
    for row in rows:
        one_row = set()
        for monomial in row:
            witness = tuple(i for i in monomial if i <= n)
            one_row.add((0,) * (2 - len(witness)) + witness)
        protected.update(one_row)
        row_supports.append(one_row)

    violations = []
    for pair in sorted(protected):
        fiber = sum_fibers[sum(weights[i] for i in pair)]
        if fiber != [pair]:
            violations.append({"protected_pair": pair, "fiber": fiber})
    require(not violations, "protected sum collision: " + repr(violations))
    constant = {m: c for m, c in rows[4].items() if not any(i <= n for i in m)}
    require(constant == {(): 1}, "last packed row lacks exact constant +1")

    width = max(weights)
    targets = [2 * width + j * (2 * width + 1) for j in range(22)]
    # The conservative row bands are disjoint and leave only their own row
    # capable of contributing at a designated target.
    for j, target in enumerate(targets):
        for other, other_target in enumerate(targets):
            if j != other:
                require(abs(target - other_target) > 2 * width, "target bands overlap")

    result = {
        "status": "PASS",
        "parent_sha256": hashlib.sha256(parent_file.read_bytes()).hexdigest(),
        "weights_sha256": hashlib.sha256(weights_file.read_bytes()).hexdigest(),
        "coordinate_count": n,
        "maximum_weight": width,
        "protected_pair_count": len(protected),
        "all_pair_count": len(all_pairs),
        "distinct_pair_sums": len(sum_fibers),
        "largest_unprotected_fiber": max(map(len, sum_fibers.values())),
        "protected_violations": violations,
        "individual_weights_distinct_positive": True,
        "last_row_constant_exactly_one": True,
        "uniform_target_max": targets[-1],
        "product_degree_bound": targets[-1] + 2 * width,
        "scope": "Exact finite algebra and weight isolation; not a semantic compiler or consistency proof.",
    }
    overlap_file = data / "overlap_layout.json"
    if overlap_file.exists():
        layout = json.loads(overlap_file.read_text())
        common_order = list(range(4)) + list(range(5, 22)) + [4]
        order = [common_order[i] for i in layout["row_indices_in_common_order"]]
        targets = layout["targets"]
        signs = layout["row_signs"]
        require(sorted(order) == list(range(22)), "overlap row permutation")
        require(len(targets) == len(signs) == 22, "overlap row count")
        require(all(s in (-1, 1) for s in signs), "row sign")
        require(targets == sorted(set(targets)), "target ordering")
        require(min(targets) >= 2 * width, "negative reversed exponent risk")
        used_exponents = {}
        checks = 0
        for j, source in enumerate(order):
            for alpha in row_supports[source]:
                alpha_sum = sum(weights[k] for k in alpha)
                exponent = targets[j] - alpha_sum
                require(exponent not in used_exponents, "D exponent collision")
                used_exponents[exponent] = (j, alpha)
                for i, target in enumerate(targets):
                    fiber = sum_fibers.get(target - targets[j] + alpha_sum, [])
                    require(not fiber or (i == j and fiber == [alpha]),
                            "contaminated output: " + repr((i, j, alpha, fiber)))
                    checks += len(all_pairs)
        last_constant = {m: signs[-1] * c for m, c in rows[order[-1]].items()
                         if not any(i <= n for i in m)}
        require(len(last_constant) == 1 and () in last_constant and last_constant[()] > 0,
                "overlap leading constant not fixed positive")
        require(max(used_exponents) == targets[-1], "overlap leading exponent")
        result["overlap"] = {
            "layout_sha256": hashlib.sha256(overlap_file.read_bytes()).hexdigest(),
            "all_pair_output_conditions": checks,
            "distinct_D_exponents": len(used_exponents),
            "target_max": targets[-1],
            "product_degree_bound": targets[-1] + 2 * width,
            "last_original_row_one_based": order[-1] + 1,
            "last_constant_after_sign": last_constant[()],
            "D_leading_coefficient": 2 * last_constant[()],
            "status": "PASS",
        }
    return result


if __name__ == "__main__":
    require(len(sys.argv) == 2, "supply the package directory")
    print(json.dumps(audit(sys.argv[1]), indent=2))
