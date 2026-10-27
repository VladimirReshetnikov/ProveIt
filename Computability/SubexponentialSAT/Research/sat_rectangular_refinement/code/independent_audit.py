#!/usr/bin/env python3
"""Independently reconstruct finite certificates from data/certificate.json.

Usage: python3 code/independent_audit.py [--data path/to/certificate.json]
The Python standard library is sufficient. This script imports no other
archive code, needs no source checkout or network, and never writes files.
It prints one JSON object on success. Explicit checks remain active under -O.

A run exhausts 84 * 72**3 = 31,352,832 root support triples plus all pair
certificates. Runtime depends on the Python interpreter and host CPU.
The result audits finite inequalities and schedule arithmetic, not the
imported SAT, deformation, or matrix-multiplication theorems.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import comb, isqrt
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def plans_for(r, entry):
    if "plans" in entry:
        return entry["plans"]
    return [[[(v + shift) % r for v in block] for block in entry["cyclic_seed"]]
            for shift in range(r)]


def make_supports(r, plan, coefficient_permutations):
    require(len(plan) == 3 and all(plan), "three nonempty blocks required")
    require(sorted(v for block in plan for v in block) == list(range(r)),
            "plan is not a partition")
    operations = []

    def divide(vertices):
        if len(vertices) == 1:
            return
        middle = len(vertices) // 2
        left, right = vertices[:middle], vertices[middle:]
        divide(left)
        divide(right)
        outside = [v for v in range(r) if v not in vertices]
        operations.append([left, right, outside])

    for block in plan:
        divide(block)
    operations.append(plan)
    require(len(operations) == r - 2, "an internal operation is missing")
    edges = list(combinations(range(r), 2))
    class_pairs = list(combinations(range(3), 2))
    supports = []
    for operation in operations:
        labels = {v: i for i, block in enumerate(operation) for v in block}
        for coefficients in coefficient_permutations:
            vector = []
            for u, v in edges:
                if labels[u] == labels[v]:
                    vector.append(0)
                else:
                    pair = tuple(sorted((labels[u], labels[v])))
                    vector.append(coefficients[class_pairs.index(pair)])
            supports.append(vector)
    require(len(supports) == len(coefficient_permutations) * (r - 2),
            "incorrect support count")
    return supports


def dot(v, w):
    return sum(a * b for a, b in zip(v, w))


def reconstruct_certificates(data):
    backend = data["backends"]["new"]
    scale = backend["scale"]
    coefficients = sorted({p for row in backend["triples"] for p in permutations(row)})
    require(len(coefficients) == 9, "the frozen backend requires nine coefficient triples")
    records = []
    for text_r, entry in data["menus"].items():
        r = int(text_r)
        plans = plans_for(r, entry)
        q = len(plans)
        weights = entry.get("weights", [1] * q)
        total_weight = sum(weights)
        require(len(weights) == q and min(weights) >= 0 and total_weight > 0,
                "invalid mixing weights")
        supports = [make_supports(r, plan, coefficients) for plan in plans]
        norms = [[weights[i] ** 2 * dot(v, v) for v in family]
                 for i, family in enumerate(supports)]
        if q == 1:
            require(entry["method"] == "single", "single-plan method mismatch")
            upper = Q(max(norms[0]), total_weight ** 2)
            terms, choices = 1, len(supports[0])
        elif entry["method"] == "pairs":
            total = 0
            choices = 0
            for i, j in combinations(range(q), 2):
                total += max(
                    norms[i][a] + norms[j][b]
                    + 2 * (q - 1) * weights[i] * weights[j] * dot(v, w)
                    for a, v in enumerate(supports[i])
                    for b, w in enumerate(supports[j]))
                choices += len(supports[i]) * len(supports[j])
            upper = Q(total, (q - 1) * total_weight ** 2)
            terms = comb(q, 2)
        else:
            require(entry["method"] == "triples" and q == 9,
                    "the independent root specialization requires nine plans")
            cross = {
                (i, j): [[8 * weights[i] * weights[j] * dot(v, w)
                          for w in supports[j]] for v in supports[i]]
                for i, j in combinations(range(q), 2)}
            total = 0
            for i, j, k in combinations(range(q), 3):
                best = 0
                for a in range(len(supports[i])):
                    for b in range(len(supports[j])):
                        fixed = norms[i][a] + norms[j][b] + cross[i, j][a][b]
                        for c in range(len(supports[k])):
                            value = (fixed + norms[k][c]
                                     + cross[i, k][a][c] + cross[j, k][b][c])
                            if value > best:
                                best = value
                total += best
            upper = Q(total, 28 * total_weight ** 2)
            terms = 84
            choices = sum(len(supports[i]) * len(supports[j]) * len(supports[k])
                          for i, j, k in combinations(range(q), 3))
        beta_squared = 2 * upper / (scale ** 2 * r ** 2)
        require(beta_squared == Q(entry["expected_beta_squared"]),
                "independent local coefficient mismatch at r=" + text_r)
        records.append({
            "groups": r, "plans": q, "operations_per_plan": r - 2,
            "supports_per_plan": len(supports[0]), "certificate_terms": terms,
            "support_choices_checked": choices,
            "beta_squared": str(beta_squared), "expected_matches": True})
    return records


def sqrt_bounds(value):
    value = Q(value)
    require(value >= 0, "negative square-root input")
    denominator = 10 ** 28
    numerator = isqrt(value.numerator * denominator ** 2 // value.denominator)
    lower, upper = Q(numerator, denominator), Q(numerator + 1, denominator)
    require(lower ** 2 <= value < upper ** 2, "square-root enclosure failed")
    return lower, upper


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def times(a, b):
    require(min(a) >= 0 and min(b) >= 0, "positive product required")
    return a[0] * b[0], a[1] * b[1]


def quotient(a, b):
    require(a[0] >= 0 and b[0] > 0, "positive quotient required")
    return a[0] / b[1], a[1] / b[0]


def point(x):
    return Q(x), Q(x)


def independent_kappa():
    # Alternating arctangent sums with 60 terms; no decimal constants are inputs.
    def atan_reciprocal(n):
        terms = [Q((-1) ** j, (2 * j + 1) * n ** (2 * j + 1))
                 for j in range(61)]
        left, right = sum(terms[:-1], Q(0)), sum(terms, Q(0))
        return min(left, right), max(left, right)
    a, b = atan_reciprocal(5), atan_reciprocal(239)
    pi = 16 * a[0] - 4 * b[1], 16 * a[1] - 4 * b[0]
    log_lower = 2 * sum((Q(1, (2 * j + 1) * 3 ** (2 * j + 1))
                         for j in range(60)), Q(0))
    log_tail = Q(2, 121 * 3 ** 121) / Q(8, 9)
    return quotient(times(pi, sqrt_bounds(2)), (log_lower, log_lower + log_tail))


def logarithm_gate(r, upper):
    upper = Q(upper)
    if upper.denominator == 1 and r == 2 ** upper.numerator:
        return
    require(r ** upper.denominator < 2 ** upper.numerator,
            "invalid rational logarithm upper bound")


def certify_schedule(data, local_certificates):
    schedule = data["schedule"]
    groups = schedule["groups"]
    etas = list(map(Q, schedule["etas"]))
    ratio = Q(schedule["tail_ratio"])
    logs = list(map(Q, schedule["log2_upper"]))
    require(len(groups) == len(etas) == len(logs), "schedule lengths differ")
    require(all(x > 0 for x in etas) and 0 < ratio < 1, "invalid taper fractions")
    caps, cumulative = [], Q(0)
    for eta in etas[:-1]:
        cumulative += eta
        caps.append(cumulative)
    caps.append(cumulative + etas[-1] / (1 - ratio))
    require(caps == list(map(Q, schedule["cumulative_caps"])), "cumulative cap mismatch")
    gaps = []
    for i, (r, cap, logarithm) in enumerate(zip(groups, caps, logs)):
        logarithm_gate(r, logarithm)
        gaps.append(Q(1, 10) - (2 if i == 0 else 1) * cap * logarithm)
    require(min(gaps) > 0, "nonpositive degree gate")
    require(caps[-1] * (1 + 2 * max(logs)) < 1, "fresh-side gate failed")
    require(groups[-1] == 4 and Q(1, 2) < Q(11, 20) < ratio,
            "tail bootstrap failed")
    kappa = independent_kappa()
    by_group = {record["groups"]: Q(record["beta_squared"])
                for record in local_certificates}
    masses = [Q(1)]
    for r in groups[:-1]:
        masses.append(masses[-1] * Q(2, r))
    local_k = [quotient(times(kappa, point(mass)), sqrt_bounds(eta))
               for mass, eta in zip(masses, etas)]
    alpha = [sqrt_bounds(Q(2 * (r - 1), r * r)) for r in groups]
    beta = [sqrt_bounds(by_group[r]) for r in groups]
    prefix, branches, spaces = point(0), [], []
    for i in range(len(groups) - 1):
        space = times(beta[i], local_k[i])
        spaces.append(space)
        branches.append(plus(prefix, space))
        prefix = plus(prefix, times(alpha[i], local_k[i]))
    gamma = quotient(point(Q(2, groups[-1])), sqrt_bounds(ratio))
    tail_multiplier = quotient(alpha[-1], (1 - gamma[1], 1 - gamma[0]))
    require(tail_multiplier[0] > beta[-1][1], "tail endpoint is not dominant")
    branches.append(plus(prefix, times(tail_multiplier, local_k[-1])))
    spaces.append(times(beta[-1], local_k[-1]))
    require(branches[-1][0] > max(x[1] for x in branches[:-1]), "time maximum changed")
    require(spaces[0][0] > max(x[1] for x in spaces[1:]), "space maximum changed")
    require(branches[-1][1] < Q(schedule["safe_time"]), "unsafe time coefficient")
    require(spaces[0][1] < Q(schedule["safe_space"]), "unsafe space coefficient")
    return {
        "strict_degree_gaps": list(map(str, gaps)), "masses": list(map(str, masses)),
        "time_interval": list(map(str, branches[-1])),
        "space_interval": list(map(str, spaces[0])),
        "safe_time": schedule["safe_time"], "safe_space": schedule["safe_space"],
        "all_branch_and_gate_checks_passed": True}


def rejects(function, expected_message):
    try:
        function()
    except ValueError as error:
        require(str(error) == expected_message, "negative control failed for an unexpected reason")
        return {"rejected": True, "reason": str(error)}
    raise ValueError("negative control was incorrectly accepted")


def negative_controls(data, schedule_result):
    backend = data["backends"]["new"]
    broken_coefficients = sorted({p for row in [[0, 0, 0], backend["triples"][1]]
                                  for p in permutations(row)})

    def missing_io():
        dimensions = (1, 1, 0)
        upper = max(dot(p, dimensions) for p in broken_coefficients)
        require(upper >= 2 * backend["scale"], "unpaid input/output size")

    def unsafe_time():
        require(Q(schedule_result["time_interval"][1]) < Q("28.43"),
                "unsafe time coefficient")

    controls = {
        "missing_io_branch": rejects(missing_io, "unpaid input/output size"),
        "false_time_28_43": rejects(unsafe_time, "unsafe time coefficient"),
        "underestimated_log2_10": rejects(lambda: logarithm_gate(10, Q("3.32")),
                                          "invalid rational logarithm upper bound"),
        "duplicate_partition_vertex": rejects(
            lambda: make_supports(4, [[0, 1], [2], [2]], [(0, 1, 1)]),
            "plan is not a partition")}
    require(comb(8, 2) == 28 and 7 * 8 == 2 * 28, "triple counting identity failed")
    controls["triple_identity"] = {
        "diagonal_multiplicity": 28, "cross_multiplicity": 56,
        "normalizing_divisor": 28, "cross_after_division": 2}
    return controls


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "certificate.json")
    arguments = parser.parse_args()
    data = json.loads(arguments.data.read_text(encoding="utf-8"))
    certificates = reconstruct_certificates(data)
    schedule = certify_schedule(data, certificates)
    result = {
        "status": "PASS",
        "scope": "Independent finite support reconstruction and paid schedule arithmetic; imported algorithmic interfaces are not re-proved.",
        "results": certificates, "all_exact_values_match": True,
        "schedule": schedule, "negative_controls": negative_controls(data, schedule),
        "runtime_inputs": {
            "data": "The selected certificate JSON is the only file read.",
            "dependencies": "Python standard library only; no other archive modules are imported.",
            "root_support_choices": 31352832,
            "outputs": "JSON on stdout; no files are written."}}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
