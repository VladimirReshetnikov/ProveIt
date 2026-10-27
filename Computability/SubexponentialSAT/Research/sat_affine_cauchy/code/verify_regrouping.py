#!/usr/bin/env python3
"""Exact regrouping checks for affine9, cyclic13, and fixed6 cached plans.

Uses arbitrary node factors over (Z/64Z)[V]/(V^2) and at most 12 active
binary directed indices. Every other directed pair has index cardinality 1.
Compares literal enumeration against independently implemented boundary-table
merges and a final three-table contraction, for EVERY certified plan.

No fast matrix multiplication backend or end-to-end SAT solver is implemented.
Standard library only. Validation remains enabled under python -O.
"""
from collections import Counter
from itertools import combinations, product
import json
import random

from certify_affine_cyclic import plans9, plans13, supports

MODULUS = 64
ZERO = (0, 0)
ONE = (1, 0)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def add(x, y):
    return ((x[0]+y[0]) % MODULUS, (x[1]+y[1]) % MODULUS)


def mul(x, y):
    return ((x[0]*y[0]) % MODULUS,
            (x[0]*y[1]+x[1]*y[0]) % MODULUS)


def fixture(r, kind):
    """Return deterministic factors; graph choices do not depend on outcomes."""
    rng = random.Random(2026102700 + 97*r + kind)
    candidates = [(a, b) for a in range(r) for b in range(r) if a != b]
    if kind == 1:
        chosen = [(a, a+1) for a in range(r-1)]
        reverse = [(b, a) for a, b in chosen]
        rng.shuffle(reverse)
        chosen += reverse[:max(0, 12-len(chosen))]
        label = "spanning_path_and_reverses"
    else:
        if kind == 2:
            cut = r//2
            candidates = [(a, b) for a, b in candidates if (a < cut) == (b < cut)]
            label = "disconnected_components"
        else:
            label = "zero_factor" if kind == 3 else "mixed_directed_indices"
        chosen = [(0, 1), (1, 0)]
        pool = [e for e in candidates if e not in chosen]
        rng.shuffle(pool)
        chosen += pool[:min(10, len(pool))]
    edges = tuple(sorted(set(chosen)))
    require(len(edges) <= 12, "Fixture exceeded the intended enumeration size")
    incident = {v: tuple(e for e in edges if v in e) for v in range(r)}
    factors = {}
    for v in range(r):
        entries = {}
        for bits in product((0, 1), repeat=len(incident[v])):
            # Odd scalar terms for isolated vertices prevent accidental
            # zero divisors from masking their contribution to every fixture.
            constant = rng.randrange(MODULUS)
            if not incident[v]:
                constant |= 1
            entries[bits] = (constant, rng.randrange(MODULUS))
        factors[v] = entries
    zero_vertex = None
    if kind == 3:
        zero_vertex = r//2
        factors[zero_vertex] = {key: ZERO for key in factors[zero_vertex]}
    return {
        "r": r, "kind": label, "edges": edges, "incident": incident,
        "factors": factors, "zero_vertex": zero_vertex,
    }


def literal_contraction(data):
    """Independent direct definition: enumerate every active global index."""
    total = ZERO
    for bits in product((0, 1), repeat=len(data["edges"])):
        assignment = dict(zip(data["edges"], bits))
        value = ONE
        for v in range(data["r"]):
            key = tuple(assignment[e] for e in data["incident"][v])
            value = mul(value, data["factors"][v][key])
        total = add(total, value)
    return total


def boundary(data, vertices):
    vertices = frozenset(vertices)
    return tuple(e for e in data["edges"]
                 if (e[0] in vertices) != (e[1] in vertices))


def cached_contraction(data, plan):
    """Materialize every singleton entry once; contract all boundary tables."""
    r = data["r"]
    calls = Counter()
    scalar_products = Counter()
    singleton = {}
    for v in range(r):
        entry_table = {}
        for bits in product((0, 1), repeat=len(data["incident"][v])):
            calls[v] += 1
            entry_table[bits] = data["factors"][v][bits]
        singleton[v] = (data["incident"][v], entry_table)

    def merge(A, B, left, right):
        left_edges, left_values = left
        right_edges, right_values = right
        output_edges = boundary(data, frozenset(A) | frozenset(B))
        union_edges = tuple(sorted(set(left_edges) | set(right_edges)))
        # AB indices are summed; A-outside and B-outside indices survive.
        values = {key: ZERO for key in product((0, 1), repeat=len(output_edges))}
        for bits in product((0, 1), repeat=len(union_edges)):
            assignment = dict(zip(union_edges, bits))
            left_key = tuple(assignment[e] for e in left_edges)
            right_key = tuple(assignment[e] for e in right_edges)
            output_key = tuple(assignment[e] for e in output_edges)
            values[output_key] = add(values[output_key],
                                     mul(left_values[left_key], right_values[right_key]))
            scalar_products["binary_merges"] += 1
        require(set(values) == set(product((0, 1), repeat=len(output_edges))),
                "A boundary table has an incorrect index domain")
        return output_edges, values

    def build(block):
        if len(block) == 1:
            return singleton[block[0]]
        middle = len(block)//2
        A, B = block[:middle], block[middle:]
        return merge(A, B, build(A), build(B))

    tables = [build(block) for block in plan]
    triangle_edges = tuple(sorted(set().union(*(set(es) for es, _ in tables))))
    total = ZERO
    for bits in product((0, 1), repeat=len(triangle_edges)):
        assignment = dict(zip(triangle_edges, bits))
        value = ONE
        for es, values in tables:
            value = mul(value, values[tuple(assignment[e] for e in es)])
            scalar_products["final_triangle"] += 1
        total = add(total, value)
    expected = {v: 2**len(data["incident"][v]) for v in range(r)}
    require(dict(calls) == expected, "Actual singleton entry evaluations are not fully counted")
    return total, dict(calls), dict(scalar_products)


def support_selector_scores(r, plans, dimensions):
    """The exact integer fifth-power selector used in the certificate."""
    pair_dimensions = [dimensions[(a, b)]*dimensions[(b, a)]
                       for a, b in combinations(range(r), 2)]
    result = []
    for plan in plans:
        score = 0
        for mask in supports(r, plan):
            value = 1
            for N, weight in zip(pair_dimensions, mask):
                value *= N**weight
            score = max(score, value)
        result.append(score)
    return result


def independent_axis_scores(r, plans, dimensions):
    """Reconstruct actual rectangular axes without using support masks."""
    U = set(range(r))
    scores = []
    for plan in plans:
        operations = []
        def record(block):
            if len(block) == 1:
                return
            k = len(block)//2
            A, B = block[:k], block[k:]
            record(A)
            record(B)
            operations.append((set(A), set(B), U-set(block)))
        for block in plan:
            record(block)
        operations.append(tuple(set(block) for block in plan))
        operation_scores = []
        for parts in operations:
            axes = []
            for i, j in ((0, 1), (0, 2), (1, 2)):
                dimension = 1
                for a in parts[i]:
                    for b in parts[j]:
                        dimension *= dimensions[(a, b)]*dimensions[(b, a)]
                axes.append(dimension)
            numerator = (axes[0]*axes[1]*axes[2])**5
            denominator = min(axes)**3
            require(numerator % denominator == 0, "Axis fifth-power cost is not integral")
            operation_scores.append(numerator//denominator)
        scores.append(max(operation_scores))
    return scores


def main():
    rows = []
    verified_plans = 0
    cases = ((6, [[[0,1],[2,3],[4,5]]]), (9, plans9()), (13, plans13()))
    for r, plans in cases:
        for kind in range(4):
            data = fixture(r, kind)
            wanted = literal_contraction(data)
            if kind == 3:
                require(wanted == ZERO, "Zero-factor fixture does not vanish")
            active = set(data["edges"])
            dims = {(a, b): (2 if (a, b) in active else 1)
                    for a in range(r) for b in range(r) if a != b}
            scores = support_selector_scores(r, plans, dims)
            reference = independent_axis_scores(r, plans, dims)
            require(scores == reference, "Mask and independent matrix-axis scores disagree")
            selected = min(range(len(scores)), key=lambda j: (scores[j], j))
            require(scores[selected] == min(reference), "Selector did not choose least cost")
            ledger = []
            for index, plan in enumerate(plans):
                got, entry_calls, operation_calls = cached_contraction(data, plan)
                require(got == wanted,
                        f"Regrouping failed: r={r}, kind={kind}, plan={index}, {got}!={wanted}")
                ledger.append({"plan_index": index, "singleton_entry_calls": sum(entry_calls.values()),
                               "scalar_products": operation_calls})
                verified_plans += 1
            rows.append({"groups": r, "fixture": data["kind"],
                         "active_directed_indices": [list(e) for e in data["edges"]],
                         "global_assignments": 2**len(data["edges"]),
                         "literal_result": list(wanted), "zero_vertex": data["zero_vertex"],
                         "plans_checked": len(plans), "selected_plan": selected,
                         "minimum_operation_cost_power5": scores[selected],
                         "all_selector_scores": scores,
                         "expected_singleton_entry_calls": sum(2**len(es) for es in data["incident"].values()),
                         "plan_ledger": ledger})
    require(len(rows) == 12 and verified_plans == 72, "Fixture or plan coverage changed")
    require(any(row["literal_result"] != [0,0] for row in rows), "Every fixture vanished")
    print(json.dumps({"status": "PASS", "ring": "(Z/64Z)[V]/(V^2)",
                      "fixtures": len(rows), "plan_contractions_verified": verified_plans,
                      "scope": "Exact finite regrouping, fifth-power selector, and counted singleton calls; no fast matrix multiplication or SAT solver implementation",
                      "results": rows}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
