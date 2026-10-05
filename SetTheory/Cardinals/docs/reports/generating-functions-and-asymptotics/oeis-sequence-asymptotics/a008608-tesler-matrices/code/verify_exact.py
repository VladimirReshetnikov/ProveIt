#!/usr/bin/env python3
"""Fail-closed, exact finite verification for report106. No asymptotic claims.

All input rational numbers are canonical integer/fraction strings. No assertions,
floating point arithmetic, third-party packages, network access, or file writes
are used by this verifier. See README.md for the scope and independent methods.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys


FIXTURE_NAMES = ("rational_four_triangles", "rational_endpoint", "saturated_edges", "no_triangle_boundary")
COUNT_SIZES = tuple(range(8))
ROOT = Path(__file__).resolve().parent


class VerificationError(Exception):
    """A missing, malformed, or false verification obligation."""


def require(condition, code, message):
    if not condition:
        raise VerificationError(f"{code}: {message}")


def same(actual, expected, code, context):
    require(actual == expected, code, f"{context}: computed {actual!r}, expected {expected!r}")


def exact_keys(obj, keys, context):
    require(type(obj) is dict, "SCHEMA", f"{context} must be an object")
    same(set(obj), set(keys), "SCHEMA", f"{context} keys")


def integer(value, context, lo=None, hi=None):
    require(type(value) is int, "SCHEMA", f"{context} must be a JSON integer, not boolean or float")
    require(lo is None or value >= lo, "SCHEMA", f"{context} below minimum")
    require(hi is None or value <= hi, "SCHEMA", f"{context} above maximum")
    return value


def rational(value, context):
    require(type(value) is str and re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", value) is not None,
            "RATIONAL", f"{context} must be a canonical rational string")
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise VerificationError(f"RATIONAL: {context}: {exc}") from exc
    same(str(result), value, "RATIONAL", f"{context} canonical representation")
    return result


def vector(raw, length, context):
    require(type(raw) is list and len(raw) == length, "SCHEMA", f"{context} has wrong vector length")
    return tuple(rational(value, f"{context}[{i}]") for i, value in enumerate(raw))


def duplicate_guard(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "SCHEMA", f"duplicate JSON object key {key!r}")
        out[key] = value
    return out


def reject_constant(value):
    raise VerificationError(f"SCHEMA: invalid JSON numeric constant {value}")


def load_json(path):
    try:
        with Path(path).open("r", encoding="utf-8") as stream:
            return json.load(stream, object_pairs_hook=duplicate_guard, parse_constant=reject_constant)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"INPUT: cannot read {path}: {exc}") from exc


def cells(n):
    return tuple((a, b) for a in range(1, n + 1) for b in range(a, n + 1))


def parse_cells(raw, n, context, complete):
    require(type(raw) is list, "SCHEMA", f"{context} must be a cell list")
    result = {}
    for k, item in enumerate(raw):
        exact_keys(item, ("a", "b", "value"), f"{context}[{k}]")
        a = integer(item["a"], context + ".a", 1, n)
        b = integer(item["b"], context + ".b", a, n)
        require((a, b) not in result, "SCHEMA", f"duplicate cell {(a, b)} in {context}")
        result[a, b] = rational(item["value"], f"{context}[{a},{b}]")
    if complete:
        same(set(result), set(cells(n)), "SCHEMA", f"{context} complete support")
    else:
        require(len(result) > 0, "SCHEMA", f"{context} cannot be empty")
        require(all(v != 0 for v in result.values()), "SCHEMA", f"{context} contains a redundant zero change")
    return result


def cuts(flow, n):
    return tuple(sum((v for (a, b), v in flow.items() if a <= i <= b), Fraction(0))
                 for i in range(1, n + 1))


def graph_data(flow, n):
    # Separate edge accumulation, not differences of the cut evaluator.
    outgoing = [Fraction(0)] * (n + 1)
    incoming = [Fraction(0)] * (n + 1)
    for (a, b), v in flow.items():
        outgoing[a - 1] += v
        incoming[b] += v
    return (tuple(outgoing[i] - incoming[i] for i in range(n + 1)),
            tuple(outgoing[:-1]), tuple(incoming[1:]))


def verify_flow(flow, n, context, integral=False):
    same(set(flow), set(cells(n)), "SUPPORT", context)
    require(all(v >= 0 for v in flow.values()), "NONNEGATIVE", context + " has a negative edge")
    if integral:
        require(all(v.denominator == 1 for v in flow.values()), "INTEGRAL", context + " has a noninteger edge")
    loads = cuts(flow, n)
    same(loads, tuple(map(Fraction, range(1, n + 1))), "CUT", context + " staircase cuts")
    netflow, rows, cols = graph_data(flow, n)
    same(netflow, tuple([Fraction(1)] * n + [Fraction(-n)]), "NETFLOW", context)
    telescoped = (loads[0],) + tuple(loads[i] - loads[i - 1] for i in range(1, n)) + (-loads[-1],)
    same(netflow, telescoped, "CUT_NETFLOW", context)
    same(sum(rows), sum(cols), "MARGIN_TOTAL", context)
    same(rows[0], Fraction(1), "THROUGHPUT", context + " source row")
    same(cols[-1], Fraction(n), "THROUGHPUT", context + " sink column")
    for j in range(1, n):
        same(cols[j - 1], rows[j] - 1, "THROUGHPUT", f"{context} internal vertex {j}")
    for j, row in enumerate(rows):
        require(1 <= row <= j + 1, "THROUGHPUT_BOUND", f"{context} row {j}")
    return loads, netflow, rows, cols


def ceiling(x):
    return -((-x.numerator) // x.denominator)


def floor(x):
    return x.numerator // x.denominator


def apply_move(flow, move, t):
    result = dict(flow)
    for cell, coefficient in move.items():
        result[cell] += t * coefficient
    return result


def canonical_hash(value):
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def verify_fixture(raw, expected):
    exact_keys(raw, ("name", "n", "cutoff_M", "q", "completed", "triangles"), "fixture")
    name = raw["name"]
    require(type(name) is str and name in FIXTURE_NAMES, "SCHEMA", "unknown fixture name")
    n = integer(raw["n"], name + ".n", 1, 30)
    cutoff = integer(raw["cutoff_M"], name + ".cutoff_M", 1, n + 1)
    exact_keys(expected, ("n", "cutoff_M", "q_cut_loads", "cut_loads", "netflow", "rows", "columns",
                          "triangle_choices", "choice_product", "margin_vector_sha256"), name + " expected")
    same(n, integer(expected["n"], "expected n", 1, 30), "FIXTURE", name)
    same(cutoff, integer(expected["cutoff_M"], "expected cutoff", 1, n + 1), "FIXTURE", name)
    q = parse_cells(raw["q"], n, name + ".q", True)
    flow = parse_cells(raw["completed"], n, name + ".completed", True)
    require(all(v >= 0 for v in q.values()), "NONNEGATIVE", name + " q has a negative edge")
    require(all(v == 0 for (a, b), v in q.items() if a < cutoff), "CUTOFF", name + " q begins before cutoff")
    q_loads = cuts(q, n)
    same(q_loads, vector(expected["q_cut_loads"], n, name + ".expected q loads"), "Q_CUT", name)
    require(all(v <= i for i, v in enumerate(q_loads, 1)), "Q_FEASIBILITY", name)
    loads, netflow, rows, cols = verify_flow(flow, n, name + " base")
    completed = dict(q)
    for i in range(1, n + 1):
        completed[i, i] += i - q_loads[i - 1]
    same(flow, completed, "COMPLETION", name + " singleton completion")
    same(loads, vector(expected["cut_loads"], n, name + ".expected cuts"), "CUT", name)
    same(netflow, vector(expected["netflow"], n + 1, name + ".expected netflow"), "NETFLOW", name)
    same(rows, vector(expected["rows"], n, name + ".expected rows"), "ROW_MARGIN", name)
    same(cols, vector(expected["columns"], n, name + ".expected columns"), "COLUMN_MARGIN", name)
    early_count = min(cutoff, n)
    same(rows[:early_count], tuple(map(Fraction, range(1, early_count + 1))), "EARLY_STAIRCASE", name)
    require(type(raw["triangles"]) is list, "SCHEMA", "triangles must be a list")
    rules = {}
    for raw_rule in raw["triangles"]:
        exact_keys(raw_rule, ("j", "changes"), name + " triangle")
        j = integer(raw_rule["j"], "triangle j", cutoff, n - 1)
        require(j not in rules, "SCHEMA", "duplicate triangle index")
        rules[j] = parse_cells(raw_rule["changes"], n, f"{name}.triangle {j}", False)
    same(set(rules), set(range(cutoff, n)), "TRIANGLE_COVERAGE", name)
    exact_keys(expected["triangle_choices"], tuple(str(j) for j in range(cutoff, n)), name + " choices")
    choices = []
    endpoints_checked = 0
    for j, rule in sorted(rules.items()):
        w = q[j, j + 1]
        require(w > 0, "TRIANGLE_WIDTH", f"{name} j={j}")
        # A unit move proves the full affine response. Test independently by
        # both cut sums and directed row/column accumulation.
        delta = {cell: rule.get(cell, Fraction(0)) for cell in cells(n)}
        same(cuts(delta, n), tuple([Fraction(0)] * n), "TRIANGLE_CUT", f"{name} j={j}")
        delta_net, delta_rows, delta_cols = graph_data(delta, n)
        same(delta_net, tuple([Fraction(0)] * (n + 1)), "TRIANGLE_NETFLOW", f"{name} j={j}")
        same(delta_rows, tuple(Fraction(i == j) for i in range(n)), "TRIANGLE_INDEPENDENCE", f"{name} j={j}")
        same(delta_cols, tuple(Fraction(i == j) for i in range(1, n + 1)), "TRIANGLE_COLUMNS", f"{name} j={j}")
        negatives = {cell for cell, v in rule.items() if v < 0}
        same(negatives, {(j, j + 1)}, "TRIANGLE_LONG_EDGE", f"{name} j={j}")
        same(rule[j, j + 1], Fraction(-1), "TRIANGLE_LONG_EDGE", f"{name} j={j}")
        # Checking both endpoints verifies nonnegativity on this real segment.
        for t in (Fraction(0), w / 2):
            moved = apply_move(flow, rule, t)
            verify_flow(moved, n, f"{name} triangle {j} t={t}")
            same(moved[j, j + 1], w - t, "HALF_EDGE", f"{name} j={j}")
            endpoints_checked += 1
        low, high = rows[j], rows[j] + w / 2
        rhos = tuple(range(ceiling(low), floor(high) + 1))
        require(len(rhos) > 0, "INTEGER_CHOICES", f"{name} j={j} has no integer throughput")
        require(len(rhos) >= floor(w / 2), "INTEGER_CHOICES", f"{name} j={j} interval point bound")
        raw_expected = expected["triangle_choices"][str(j)]
        require(type(raw_expected) is list, "SCHEMA", "expected choices must be a list")
        expected_rhos = tuple(integer(v, "rho", 1, j + 1) for v in raw_expected)
        same(rhos, expected_rhos, "INTEGER_CHOICES", f"{name} j={j}")
        choices.append(rhos)
    # Simultaneous half-width endpoints catch any nonnegativity interaction.
    at_all_endpoints = dict(flow)
    for j, rule in sorted(rules.items()):
        at_all_endpoints = apply_move(at_all_endpoints, rule, q[j, j + 1] / 2)
    verify_flow(at_all_endpoints, n, name + " simultaneous half-width endpoint")
    # Exhaust the Cartesian product; every vector is actually realized.
    records = []
    seen_rows, seen_tables = set(), set()
    for selected in itertools.product(*choices):
        moved = dict(flow)
        parameters = []
        for (j, rule), rho in zip(sorted(rules.items()), selected):
            t = Fraction(rho) - rows[j]
            require(0 <= t <= q[j, j + 1] / 2, "PARAMETER_RANGE", f"{name} j={j}")
            parameters.append((j, t))
            moved = apply_move(moved, rule, t)
        _, _, alpha, beta = verify_flow(moved, n, name + " simultaneous choice")
        target = list(rows)
        for j, t in parameters:
            target[j] += t
        same(alpha, tuple(target), "SIMULTANEOUS_INDEPENDENCE", name)
        same(alpha[:early_count], rows[:early_count], "EARLY_STAIRCASE", name)
        require(all(v.denominator == 1 and v >= 0 for v in alpha + beta), "INTEGER_MARGINS", name)
        table_key = tuple(moved[cell] for cell in cells(n))
        require(alpha not in seen_rows, "DISTINCT_MARGINS", name)
        require(table_key not in seen_tables, "DISTINCT_TABLES", name)
        seen_rows.add(alpha)
        seen_tables.add(table_key)
        # alpha=(1,rho_1,...), beta=(rho_1-1,...,n) explicitly checked.
        same(beta, tuple(v - 1 for v in alpha[1:]) + (Fraction(n),), "TABLE_MARGINS", name)
        records.append({"alpha": [str(v) for v in alpha], "beta": [str(v) for v in beta]})
    product = 1
    for candidate_list in choices:
        product *= len(candidate_list)
    same(len(records), product, "CHOICE_PRODUCT", name)
    same(product, integer(expected["choice_product"], "choice_product", 1), "CHOICE_PRODUCT", name)
    digest = expected["margin_vector_sha256"]
    require(type(digest) is str and re.fullmatch(r"[0-9a-f]{64}", digest) is not None, "SCHEMA", "invalid margin hash")
    same(canonical_hash(records), digest, "MARGIN_DIGEST", name)
    return {"name": name, "n": n, "cutoff_M": cutoff, "triangles": len(rules),
            "individual_endpoints_checked": endpoints_checked, "distinct_integer_margin_vectors": product,
            "margin_vector_sha256": digest}


def weak_compositions(total, slots):
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in weak_compositions(total - first, slots - 1):
            yield (first,) + tail


@lru_cache(maxsize=None)
def hook_recurrence(hooks):
    """Remove first Tesler row; the last composition coordinate is diagonal.

    A row with hook h distributes h over its remaining off-diagonal entries
    and its diagonal. Off-diagonal entries increase the remaining hooks.
    This recurrence never uses intervals, cuts, or residual cut capacities.
    """
    if not hooks:
        return 1
    require(all(type(h) is int and h >= 0 for h in hooks), "HOOK", "invalid recurrence state")
    total = 0
    for composition in weak_compositions(hooks[0], len(hooks)):
        tail = tuple(hooks[k] + composition[k - 1] for k in range(1, len(hooks)))
        total += hook_recurrence(tail)
    return total


def inspect_integer_leaf(n, nonsingletons, values, remaining):
    """Check a counted object directly, using integer arithmetic only."""
    flow = dict(zip(nonsingletons, values))
    flow.update({(i, i): remaining[i - 1] for i in range(1, n + 1)})
    require(all(type(v) is int and v >= 0 for v in flow.values()), "ENUM_NONNEGATIVE", "invalid leaf")
    loads = [sum(v for (a, b), v in flow.items() if a <= i <= b) for i in range(1, n + 1)]
    same(loads, list(range(1, n + 1)), "ENUM_CUT", f"n={n}")
    outgoing, incoming = [0] * (n + 1), [0] * (n + 1)
    matrix = [[0] * n for _ in range(n)]
    for (a, b), v in flow.items():
        outgoing[a - 1] += v
        incoming[b] += v
        # Edge(i,j), j<n maps to Tesler A[i,j]; edge(i,n) to A[i,i].
        i = a - 1
        matrix[i][i if b == n else b] = v
    same([outgoing[i] - incoming[i] for i in range(n + 1)], [1] * n + [-n], "ENUM_NETFLOW", f"n={n}")
    same(sum(outgoing), sum(incoming), "ENUM_MARGINS", f"n={n}")
    for i in range(n):
        hook = sum(matrix[i][i:]) - sum(matrix[k][i] for k in range(i))
        same(hook, 1, "ENUM_HOOK", f"n={n}, row={i}")
    # Invert the edge-to-Tesler mapping, testing its indexing and bijectivity.
    roundtrip = {}
    for i in range(n):
        roundtrip[i + 1, n] = matrix[i][i]
        for j in range(i + 1, n):
            roundtrip[i + 1, j] = matrix[i][j]
    same(roundtrip, flow, "ENUM_BIJECTION", f"n={n}")
    return tuple(outgoing[1:n])


def enumerate_nonsingletons(n):
    """Exhaust all nonsingleton multiplicities under the individual cut caps."""
    if n == 0:
        return 1, 1
    intervals = tuple((a, b) for a in range(1, n + 1) for b in range(a + 1, n + 1))
    remaining = list(range(1, n + 1))
    values = [0] * len(intervals)
    margins = Counter()

    def visit(index):
        if index == len(intervals):
            rho = inspect_integer_leaf(n, intervals, values, remaining)
            margins[rho] += 1
            return 1
        a, b = intervals[index]
        cap = min(remaining[a - 1:b])
        subtotal = 0
        for multiplicity in range(cap + 1):
            values[index] = multiplicity
            for cut in range(a - 1, b):
                remaining[cut] -= multiplicity
            subtotal += visit(index + 1)
            for cut in range(a - 1, b):
                remaining[cut] += multiplicity
        return subtotal

    count = visit(0)
    same(sum(margins.values()), count, "ENUM_MARGIN_PARTITION", f"n={n}")
    same(remaining, list(range(1, n + 1)), "ENUM_RESTORE", f"n={n}")
    return count, len(margins)


def verify_counts(expected):
    exact_keys(expected, tuple(str(n) for n in COUNT_SIZES), "small_counts")
    results = []
    for n in COUNT_SIZES:
        target = integer(expected[str(n)], f"small_counts[{n}]", 1)
        by_hooks = hook_recurrence((1,) * n)
        by_cuts, margin_classes = enumerate_nonsingletons(n)
        same(by_hooks, by_cuts, "COUNT_AGREEMENT", f"n={n}")
        same(by_hooks, target, "EXPECTED_COUNT", f"n={n}")
        results.append({"n": n, "hook_recurrence": by_hooks, "nonsingleton_enumeration": by_cuts,
                        "expected": target, "throughput_classes": margin_classes})
    return results


def run(fixtures_path, expected_path):
    fixtures = load_json(fixtures_path)
    expected = load_json(expected_path)
    exact_keys(fixtures, ("schema_version", "scope", "fixtures"), "fixtures document")
    exact_keys(expected, ("schema_version", "sequence_source", "indexing", "small_counts", "fixtures"), "expected document")
    same(integer(fixtures["schema_version"], "schema_version"), 1, "SCHEMA", "fixtures version")
    same(integer(expected["schema_version"], "schema_version"), 1, "SCHEMA", "expected version")
    for value, context in ((fixtures["scope"], "scope"), (expected["sequence_source"], "sequence_source"), (expected["indexing"], "indexing")):
        require(type(value) is str and len(value) > 0, "SCHEMA", context + " must be a nonempty string")
    same(expected["sequence_source"], "https://oeis.org/A008608", "SCHEMA", "sequence source")
    require(type(fixtures["fixtures"]) is list, "SCHEMA", "fixtures must be a list")
    require(all(type(f) is dict and type(f.get("name")) is str for f in fixtures["fixtures"]), "SCHEMA", "bad fixture record")
    names = [f["name"] for f in fixtures["fixtures"]]
    same(names, list(FIXTURE_NAMES), "FIXTURE_COVERAGE", "all fixtures in canonical order")
    exact_keys(expected["fixtures"], FIXTURE_NAMES, "expected fixtures")
    fixture_results = [verify_fixture(f, expected["fixtures"][f["name"]]) for f in fixtures["fixtures"]]
    count_results = verify_counts(expected["small_counts"])
    return {"status": "PASS", "arithmetic": "exact integers and fractions.Fraction", "python_optimization": sys.flags.optimize,
            "scope": "Finite algebraic fixtures and exhaustive n<=7 counting; no asymptotic or floating-point claim.",
            "fixtures": fixture_results, "small_counts": count_results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=ROOT / "rational_fixtures.json")
    parser.add_argument("--expected", type=Path, default=ROOT / "expected_checks.json")
    args = parser.parse_args()
    try:
        result = run(args.fixtures, args.expected)
    except Exception as exc:
        # Unexpected exceptions also fail closed and cannot produce a PASS.
        print(f"FAIL {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
