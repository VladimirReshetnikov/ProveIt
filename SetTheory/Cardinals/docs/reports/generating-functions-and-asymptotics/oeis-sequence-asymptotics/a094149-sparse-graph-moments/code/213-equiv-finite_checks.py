#!/usr/bin/env python3
"""Fresh exact finite computations for Report213, with no external dependencies.

All checks precede output creation. Finite checks are not an asymptotic proof.
"""
import argparse
from collections import Counter
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import csv
import io
import sys
sys.dont_write_bytecode = True
from common import (MAX_K, ENUM_K, SELECTED_K, RESULT_FILES, bells, branch,
                    decimal_ratio, exact_ratio, json_bytes, majorant,
                    multiply_truncated, partition_sizes, recurrence, require,
                    sha256, unique_json)

MATH_GUARDS = (
    "initial_values", "root_boundary", "one_defect", "strict_increase",
    "rough_bound", "moment_power", "branch_formula", "branch_bound",
    "walk_encoding", "hub_bound", "enumerated_root_row", "rotation",
    "maximum_cap", "first_edge", "branch_cuts", "partition_exact",
    "partition_majorant", "exponential_coefficient", "root_majorant",
    "A_t_identity", "double_hub", "union_identity", "fresh_partition",
    "bell_convolution",
)


class Audit:
    def __init__(self, injection):
        self.injection = injection
        self.counts = Counter()

    def equal(self, lhs, rhs, name, context=None):
        checked = lhs + 1 if self.injection == name else lhs
        require(checked == rhs, name, context)
        self.counts[name] += 1

    def at_most(self, lhs, rhs, name, context=None):
        checked = rhs + 1 if self.injection == name else lhs
        require(checked <= rhs, name, context)
        self.counts[name] += 1


def enumerate_walks(k, audit):
    """Generate each first-appearance-normalized closed tree walk exactly once.

    The only moves follow a discovered neighbor or discover the next new vertex.
    No F/E recurrence, stored moments, partitions, or Bell values drive generation.
    """
    parents, children, departures, depth = [-1], [[]], [0], [0]
    directions, choices = [], []
    roots, occupancy, maxima = Counter(), Counter(), Counter()
    thresholds = range(k // 2 + 1, k + 1)
    unions, doubles, hub_totals = Counter(), Counter(), Counter()
    codes = set()

    def visit(cur, step):
        if step == 2 * k:
            if cur != 0:
                return
            roots[departures[0]] += 1
            occupancy.update(departures)
            maximum = max(departures)
            maxima[maximum] += 1
            audit.at_most(max(choices), maximum, "walk_encoding", (k, maximum))
            code = (tuple(directions), tuple(choices))
            audit.equal(int(code in codes), 0, "walk_encoding", k)
            codes.add(code)
            for threshold in thresholds:
                hubs = sum(d >= threshold for d in departures)
                audit.at_most(hubs, 2, "hub_bound", (k, threshold))
                unions[threshold] += hubs > 0
                doubles[threshold] += hubs == 2
                hub_totals[threshold] += hubs
            return
        remaining = 2 * k - step
        if depth[cur] > remaining or (remaining - depth[cur]) % 2:
            return
        departures[cur] += 1
        if parents[cur] >= 0:
            directions.append(-1)
            visit(parents[cur], step + 1)
            directions.pop()
        for i, nxt in enumerate(children[cur]):
            directions.append(1)
            choices.append(i + 1)
            visit(nxt, step + 1)
            choices.pop()
            directions.pop()
        if depth[cur] + 1 <= remaining - 1:
            nxt = len(parents)
            children[cur].append(nxt)
            parents.append(cur)
            children.append([])
            departures.append(0)
            depth.append(depth[cur] + 1)
            directions.append(1)
            choices.append(len(children[cur]))
            visit(nxt, step + 1)
            choices.pop()
            directions.pop()
            depth.pop()
            departures.pop()
            children.pop()
            parents.pop()
            children[cur].pop()
        departures[cur] -= 1

    visit(0, 0)
    audit.equal(len(codes), sum(roots.values()), "walk_encoding", k)
    return roots, occupancy, maxima, unions, doubles, hub_totals


def cut_count(excursions, slots):
    """Count ordered weak compositions directly; no binomial formula is used."""
    if slots == 1:
        return 1
    return sum(cut_count(excursions - first, slots - 1)
               for first in range(excursions + 1))


def exponential_majorant_coefficient(a, m, s):
    """Independent rational coefficient computation via d(exp Q)/dx=Q' exp Q."""
    e = [[Fraction(0) for _ in range(s + 1)] for _ in range(m + 1)]
    e[0][0] = Fraction(1)
    for r in range(1, m + 1):
        for u in range(s + 1):
            e[r][u] = sum(Fraction(q, r * factorial(q)) * a[t]
                          * comb(q + t - 1, t) * e[r - q][u - t]
                          for q in range(1, r + 1) for t in range(u + 1))
    return factorial(m) * e[m][s]


def csv_bytes(header, rows):
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(header)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def compute(injection=None):
    audit = Audit(injection)
    f, e = recurrence(MAX_K)
    a = [sum(row) for row in f]
    b = bells(MAX_K + 1)
    audit.equal(a[0], 1, "initial_values", 0)
    audit.equal(a[1], 1, "initial_values", 1)
    for k in range(1, MAX_K + 1):
        audit.equal(f[k][1], a[k - 1], "root_boundary", (k, 1))
        audit.equal(f[k][k], b[k], "root_boundary", (k, k))
        if k >= 2:
            audit.equal(f[k][k - 1], (k - 1) * b[k - 1], "one_defect", k)
            audit.at_most(a[k - 1] + 1, a[k], "strict_increase", k)
        catalan = comb(2 * k, k) // (k + 1)
        audit.at_most(a[k], catalan * factorial(k), "rough_bound", k)
        audit.at_most(catalan * factorial(k), 4 ** (k - 1) * factorial(k), "rough_bound", k)
        for t in range(k + 1):
            audit.at_most(a[t] ** k, a[k] ** t, "moment_power", (t, k))
    for t in range(MAX_K):
        for q in range(1, MAX_K - t + 1):
            audit.equal(e[t][q], branch(f, t, q), "branch_formula", (t, q))
            lower = comb(q + t - 1, t)
            audit.at_most(lower, e[t][q], "branch_bound", (t, q, "lower"))
            audit.at_most(e[t][q], a[t] * lower, "branch_bound", (t, q, "upper"))

    enumerated = [[1]]
    enum_rows, rotation_rows, two_hub_rows = [], [], []
    independent_walks = 0
    for k in range(1, ENUM_K + 1):
        roots, occupancy, maxima, unions, doubles, hub_totals = enumerate_walks(k, audit)
        row = [roots[j] for j in range(k + 1)]
        enumerated.append(row)
        independent_walks += sum(row)
        enum_rows.append({"k": k, "a_k": sum(row), "F_k_1_through_k": row[1:]})
        for m in range(1, k + 1):
            audit.equal(row[m], f[k][m], "enumerated_root_row", (k, m))
            weighted = Fraction(2 * k * row[m], m)
            audit.equal(weighted, occupancy[m], "rotation", (k, m))
            rotation_rows.append({"k": k, "m": m, "vertex_occurrences": occupancy[m],
                                  "weighted_root_count": exact_ratio(weighted)})
        catalan = comb(2 * k, k) // (k + 1)
        for cap in range(1, k + 1):
            observed = sum(count for maximum, count in maxima.items() if maximum <= cap)
            audit.at_most(observed, catalan * cap ** k, "maximum_cap", (k, cap))
        for threshold in range(k // 2 + 1, k + 1):
            weighted = sum((Fraction(2 * k * row[m], m)
                            for m in range(threshold, k + 1)), Fraction(0))
            audit.equal(weighted, hub_totals[threshold], "rotation", (k, threshold, "tail"))
            double_formula = Fraction(0)
            for q in range(1, k + 1):
                minimum = max(0, threshold - q)
                double_formula += Fraction(k, q) * sum(
                    branch(enumerated, t, q, minimum)
                    * branch(enumerated, k - q - t, q, minimum)
                    for t in range(k - q + 1))
            audit.equal(double_formula, doubles[threshold], "double_hub", (k, threshold))
            audit.equal(weighted - double_formula, unions[threshold], "union_identity", (k, threshold))
            two_hub_rows.append({"k": k, "threshold": threshold,
                                 "weighted_vertices": int(weighted), "double_hub_walks": doubles[threshold],
                                 "union_walks": unions[threshold]})

    for t in range(ENUM_K):
        for q in range(1, ENUM_K - t + 1):
            counted = sum(enumerated[t][j] * cut_count(j, q) for j in range(t + 1))
            audit.equal(counted, e[t][q], "branch_cuts", (t, q))
    g = majorant(a, MAX_K)
    for k in range(1, ENUM_K + 1):
        for m in range(1, k + 1):
            candidate = sum(comb(m - 1, q - 1)
                            * sum(branch(enumerated, t, q) * (enumerated[k-q-t][m-q]
                                  if m-q <= k-q-t else 0) for t in range(k-q+1))
                            for q in range(1, m + 1))
            audit.equal(candidate, enumerated[k][m], "first_edge", (k, m))
            s = k - m
            exact, major, fresh = 0, 0, 0
            for sizes in partition_sizes(m):
                exact_poly, major_poly, fresh_poly = [1] + [0] * s, [1] + [0] * s, [1] + [0] * s
                for q in sizes:
                    exact_poly = multiply_truncated(exact_poly,
                                 [branch(enumerated, t, q) for t in range(s+1)], s)
                    major_poly = multiply_truncated(major_poly,
                                 [a[t] * comb(q+t-1, t) for t in range(s+1)], s)
                    fresh_poly = multiply_truncated(fresh_poly,
                                 [comb(q+t-1, t) for t in range(s+1)], s)
                exact += exact_poly[s]
                major += major_poly[s]
                fresh += fresh_poly[s]
            audit.equal(exact, enumerated[k][m], "partition_exact", (k, m))
            audit.equal(major, g[m][s], "partition_majorant", (k, m))
            audit.equal(exponential_majorant_coefficient(a, m, s), major,
                        "exponential_coefficient", (k, m))
            audit.equal(fresh, comb(k-1, s)*b[m], "fresh_partition", (k, m))
    for k in range(1, MAX_K + 1):
        for m in range(1, k + 1):
            audit.at_most(f[k][m], g[m][k-m], "root_majorant", (k, m))
    for t in range(1, 33):
        for q in range(1, 65):
            candidate = sum(comb(t-1, j-1)*comb(q, j) for j in range(1, min(t, q)+1))
            audit.equal(candidate, comb(q+t-1, t), "A_t_identity", (t, q))
    for k in range(1, MAX_K + 1):
        audit.equal(sum(comb(k-1, s)*b[k-s] for s in range(k)), b[k+1]-b[k],
                    "bell_convolution", k)
    require(set(audit.counts) == set(MATH_GUARDS), "guard_coverage", sorted(audit.counts))

    table_rows = []
    for k in SELECTED_K:
        ratio = Fraction(a[k], 2*b[k+1])
        table_rows.append({"k": k, "a_k": str(a[k]), "B_k_plus_1": str(b[k+1]),
                           "ratio": exact_ratio(ratio), "ratio_decimal": decimal_ratio(ratio),
                           "fresh_convolution": str(b[k+1]-b[k])})
    checks = {
        "schema": "Report213.finite-checks.v1",
        "all_checks_passed": True,
        "scope": {
            "fresh_recurrence_max_k": MAX_K,
            "independent_exhaustive_walk_enumeration_max_k": ENUM_K,
            "independently_enumerated_walks_k1_through_k8": independent_walks,
            "partition_and_rational_exponential_checks_max_k": ENUM_K,
            "integer_majorant_max_k": MAX_K,
            "A_t_binomial_identity_t_max": 32,
            "A_t_binomial_identity_q_max": 64,
            "arithmetic": "Unbounded Python integers and fractions.Fraction; Decimal is used only for final display.",
            "limitation": "Finite identities and inequalities only. These computations establish no asymptotic bound, effective onset, error constant, or inverse accuracy radius.",
        },
        "guard_counts": dict(audit.counts),
        "root_array_sha256": sha256(json_bytes([row[:k+1] for k, row in enumerate(f)])),
        "enumerated_rows": enum_rows,
        "weighted_rotation": rotation_rows,
        "two_hub_checks": two_hub_rows,
        "selected_table": table_rows,
    }
    header = ["k", "a_k", "B_k_plus_1", "ratio_numerator", "ratio_denominator", "ratio_decimal", "fresh_convolution"]
    def table_line(k):
        ratio = Fraction(a[k], 2*b[k+1])
        return [k, a[k], b[k+1], ratio.numerator, ratio.denominator, decimal_ratio(ratio), b[k+1]-b[k] if k else "N/A"]
    tex = ["% Generated by finite_checks.py; exact arithmetic before rounding.",
           "% Requires booktabs. This table is finite evidence, not an asymptotic test.",
           r"\begin{tabular}{r r r r}", r"\toprule",
           r"$k$ & $a_k$ & $B_{k+1}$ & $a_k/(2B_{k+1})$ \\", r"\midrule"]
    for item in table_rows:
        tex.append(f"{item['k']} & {item['a_k']} & {item['B_k_plus_1']} & {item['ratio_decimal']} " + r"\\")
    tex.extend([r"\bottomrule", r"\end{tabular}", ""])
    return {"checks.json": json_bytes(checks),
            "moments.csv": csv_bytes(header, [table_line(k) for k in range(MAX_K+1)]),
            "selected_table.csv": csv_bytes(header, [table_line(k) for k in SELECTED_K]),
            "table.tex": "\n".join(tex).encode("utf-8")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="A new output directory; existing paths are refused.")
    parser.add_argument("--compare", type=Path, help="Require exact agreement with this result directory before writing.")
    parser.add_argument("--inject-failure", choices=MATH_GUARDS, help="Corrupt one mathematical value immediately before its comparison.")
    args = parser.parse_args()
    require(not args.out.exists(), "output_exists", str(args.out))
    require(args.out.parent.is_dir(), "output_parent", str(args.out.parent))
    outputs = compute(args.inject_failure)
    if args.compare is not None:
        require(args.compare.is_dir() and set(p.name for p in args.compare.iterdir()) == set(RESULT_FILES)
                and all((args.compare / name).is_file() for name in RESULT_FILES),
                "reference_inventory", "Expected exactly the four documented result files")
        expected = unique_json(args.compare / "checks.json")
        import json
        require(expected == json.loads(outputs["checks.json"]), "reference_comparison", "checks.json")
        for name in RESULT_FILES:
            require((args.compare / name).read_bytes() == outputs[name], "reference_comparison", name)
    args.out.mkdir()
    for name in RESULT_FILES:
        (args.out / name).write_bytes(outputs[name])
    print(json_bytes({"all_checks_passed": True, "fresh_recurrence_max_k": MAX_K,
                      "independent_enumeration_max_k": ENUM_K,
                      "result_sha256": {name: sha256(outputs[name]) for name in RESULT_FILES}}).decode(), end="")


if __name__ == "__main__":
    main()
