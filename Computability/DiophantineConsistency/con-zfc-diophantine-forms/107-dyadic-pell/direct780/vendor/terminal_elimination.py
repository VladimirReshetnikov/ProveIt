#!/usr/bin/env python3
"""Exact degree-preserving coordinate elimination over N or Z.

This portable adapter also accepts unrestricted integer equations. Over Z,
negative restoration coefficients are also permitted: every polynomial
restoration is automatically integral. All algebraic
certificate checks and degree restrictions are unchanged.

Input: finite_quadratic_residuals_v1, with all variables in N or Z.
A row v=f can be removed if f has integer coefficients and degree <= 2,
and substitution does not raise any other row above degree 2. In the
natural domain only, the coefficients of f must also be nonnegative.
Affine f is always allowed; quadratic f is allowed only when v appears
linearly in every other row. The transformation is an exact existential
equivalence, with unique restoration of every deleted coordinate.

This is post-processing of literal equations, independent of their builder.
It uses no asserts, network, theorem prover, or satisfiability search.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, Counter
import copy
import hashlib
import json
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def normalize(terms):
    out = defaultdict(int)
    for coefficient, monomial in terms:
        out[tuple(sorted(monomial))] += coefficient
    return {m: c for m, c in out.items() if c}


def as_terms(poly):
    return [[coefficient, list(monomial)] for monomial, coefficient in sorted(poly.items())]


def multiply(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return {m: c for m, c in out.items() if c}


def substitute(poly, variable, restoration):
    result = defaultdict(int)
    for monomial, coefficient in poly.items():
        value = {(): coefficient}
        for coordinate in monomial:
            value = multiply(value, restoration if coordinate == variable else {(coordinate,): 1})
        for mon, coeff in value.items():
            result[mon] += coeff
    return {m: c for m, c in result.items() if c}


def degree(poly):
    return max((len(m) for m in poly), default=0)


def candidate(poly, variable, require_nonnegative=True):
    coefficient = poly.get((variable,), 0)
    if coefficient not in (-1, 1):
        return None
    other = {m: c for m, c in poly.items() if m != (variable,)}
    if any(variable in m for m in other):
        return None
    restored = {m: -c * coefficient for m, c in other.items()}
    if require_nonnegative and any(c < 0 for c in restored.values()):
        return None
    return restored


def optimize(equation, max_support=8, affine_support=None, quadratic_first=False):
    need(equation["domain"] in ("nonnegative integers", "unrestricted integers"), "integer or natural domain required")
    original_rows = equation["residuals"]
    rows = {i: normalize(row["terms"]) for i, row in enumerate(original_rows)}
    need(all(degree(row) <= 2 for row in rows.values()), "input must be quadratic")
    variables = equation["variables"]
    live = set(range(len(variables)))
    steps = []
    while True:
        appearances = defaultdict(set)
        nonlinear = defaultdict(set)
        for row_id, poly in rows.items():
            for monomial in poly:
                for v in set(monomial):
                    appearances[v].add(row_id)
                    if len(monomial) > 1:
                        nonlinear[v].add(row_id)
        choices = []
        for row_id, poly in rows.items():
            for monomial in poly:
                if len(monomial) != 1:
                    continue
                v = monomial[0]
                restored = candidate(poly, v, equation["domain"] == "nonnegative integers")
                if restored is None:
                    continue
                d = degree(restored)
                cap = affine_support if d <= 1 and affine_support is not None else max_support
                if len(restored) > cap:
                    continue
                if d == 2 and nonlinear[v] - {row_id}:
                    continue
                # Prefer cheap affine substitutions, then definitions of gates.
                priority = {0: 0, 1: 2, 2: 1}[d] if quadratic_first else d
                score = (priority, variables[v].get("kind") != "gate", len(restored),
                         len(appearances[v]), v, row_id)
                choices.append((score, row_id, v, restored))
        if not choices:
            break
        _, row_id, variable, restored = min(choices, key=lambda choice: choice[0])
        for other_id in sorted(appearances[variable] - {row_id}):
            new = substitute(rows[other_id], variable, restored)
            need(degree(new) <= 2, "substitution raised degree")
            if new:
                rows[other_id] = new
            else:
                del rows[other_id]
        del rows[row_id]
        live.remove(variable)
        steps.append({"row_id": row_id, "variable": variable,
                      "name": variables[variable]["name"],
                      "kind": variables[variable].get("kind"),
                      "restoration": as_terms(restored), "restoration_degree": degree(restored)})
    actually_used = {v for row in rows.values() for mon in row for v in mon}
    unused = sorted(live - actually_used)
    # Unconstrained coordinates in either domain may be restored as zero.
    ordered = sorted(actually_used)
    remap = {v: i for i, v in enumerate(ordered)}
    output = copy.deepcopy(equation)
    output["variables"] = [variables[v] for v in ordered]
    output["residuals"] = [{"label": original_rows[i]["label"],
                            "terms": [[c, [remap[v] for v in mon]] for mon, c in sorted(poly.items())]}
                           for i, poly in sorted(rows.items())]
    metrics = {
        "input_variables": len(variables), "output_variables": len(ordered),
        "input_rows": len(original_rows), "output_rows": len(rows),
        "eliminated_coordinates": len(steps), "unconstrained_removed": len(unused),
        "by_restoration_degree": dict(Counter(s["restoration_degree"] for s in steps)),
        "by_kind": dict(Counter(s["kind"] for s in steps)),
        "max_support": max_support,
        "affine_support": affine_support,
        "quadratic_first": quadratic_first,
        "max_output_row_terms": max(map(len, rows.values()), default=0),
    }
    output["metrics"] = dict(output.get("metrics", {}), variables=len(ordered),
                             quadratic_rows=len(rows), variable_kinds=dict(Counter(v.get("kind") for v in output["variables"])))
    expanded = expand(output)
    exact_metrics = {"expanded_monomials": len(expanded["terms"]),
                     "exact_degree": max((len(m) for c, m in expanded["terms"]), default=0),
                     "max_abs_expanded_coefficient": max((abs(c) for c, m in expanded["terms"]), default=0),
                     "max_abs_row_coefficient": max((abs(c) for row in output["residuals"] for c, m in row["terms"]), default=0)}
    metrics.update(exact_metrics)
    output["metrics"].update(exact_metrics)
    output["elimination"] = {"method": ("nonnegative monic quadratic substitution" if equation["domain"] == "nonnegative integers" else "integral monic quadratic substitution"),
                             "certificate": "terminal_elimination_certificate.json"}
    certificate = {"schema": ("natural_quadratic_elimination_v1" if equation["domain"] == "nonnegative integers" else "integer_quadratic_elimination_v1"),
                   "input_sha256": hashlib.sha256(canonical_bytes(equation)).hexdigest(),
                   "output_sha256": hashlib.sha256(canonical_bytes(output)).hexdigest(),
                   "steps": steps, "unconstrained_removed": unused,
                   "retained_original_variables": ordered,
                   "retained_original_rows": sorted(rows), "metrics": metrics}
    return output, certificate, metrics


def verify(equation, output, certificate):
    need(hashlib.sha256(canonical_bytes(equation)).hexdigest() == certificate["input_sha256"], "input hash")
    need(hashlib.sha256(canonical_bytes(output)).hexdigest() == certificate["output_sha256"], "output hash")
    rows = {i: normalize(row["terms"]) for i, row in enumerate(equation["residuals"])}
    deleted = set()
    for step in certificate["steps"]:
        row_id, v = step["row_id"], step["variable"]
        need(row_id in rows and v not in deleted, "invalid deletion target")
        restored = normalize(step["restoration"])
        need(v not in {x for m in restored for x in m}, "self dependency")
        need(equation["domain"] != "nonnegative integers" or all(c >= 0 for c in restored.values()), "negative natural restoration coefficient")
        need(degree(restored) <= 2, "restoration degree")
        expected = {(v,): 1}
        for mon, coefficient in restored.items():
            expected[mon] = expected.get(mon, 0) - coefficient
        expected = {m: c for m, c in expected.items() if c}
        need(rows[row_id] == expected or rows[row_id] == {m: -c for m, c in expected.items()},
             "deleted row not exactly v-f or f-v")
        if degree(restored) == 2:
            need(all(v not in mon or len(mon) == 1 for i, row in rows.items() if i != row_id for mon in row),
                 "quadratic restoration has nonlinear occurrence")
        newrows = {}
        for i, row in rows.items():
            if i == row_id:
                continue
            transformed = substitute(row, v, restored)
            need(degree(transformed) <= 2, "verification degree increase")
            if transformed:
                newrows[i] = transformed
        rows = newrows
        deleted.add(v)
    ordered = certificate["retained_original_variables"]
    need(ordered == sorted({v for row in rows.values() for m in row for v in m}), "wrong retained variables")
    remap = {v: i for i, v in enumerate(ordered)}
    literal = [{"label": equation["residuals"][i]["label"],
                "terms": [[c, [remap[v] for v in mon]] for mon, c in sorted(row.items())]}
               for i, row in sorted(rows.items())]
    need(literal == output["residuals"], "literal output mismatch")
    need([equation["variables"][v] for v in ordered] == output["variables"], "variable map mismatch")
    need(sorted(rows) == certificate["retained_original_rows"], "row map mismatch")
    need(sorted(set(range(len(equation["variables"]))) - deleted - set(ordered)) == certificate["unconstrained_removed"],
         "wrong unconstrained coordinates")
    return {"status": "PASS", "verified_steps": len(deleted),
            "output_variables": len(ordered), "output_rows": len(rows)}


def expand(equation):
    out = defaultdict(int)
    for row in equation["residuals"]:
        poly = normalize(row["terms"])
        for mon, coefficient in multiply(poly, poly).items():
            out[mon] += coefficient
    out = {m: c for m, c in out.items() if c}
    return {"schema": "sparse_integer_polynomial_v1", "domain": equation["domain"],
            "variables": len(equation["variables"]), "terms": as_terms(out)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--max-support", type=int, default=8)
    parser.add_argument("--affine-support", type=int)
    parser.add_argument("--quadratic-first", action="store_true")
    parser.add_argument("--expand", action="store_true")
    args = parser.parse_args()
    original = json.loads(args.input.read_text())
    output, certificate, metrics = optimize(original, args.max_support, args.affine_support, args.quadratic_first)
    review = verify(original, output, certificate)
    if args.expand:
        polynomial = expand(output)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, value in [("equation.json", output), ("terminal_elimination_certificate.json", certificate),
                        ("TERMINAL_ELIMINATION.json", metrics | review)]:
        (args.output_dir / name).write_bytes(canonical_bytes(value))
    if args.expand:
        (args.output_dir / "expanded_polynomial.json").write_bytes(canonical_bytes(polynomial))
    print(json.dumps(metrics | review, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
