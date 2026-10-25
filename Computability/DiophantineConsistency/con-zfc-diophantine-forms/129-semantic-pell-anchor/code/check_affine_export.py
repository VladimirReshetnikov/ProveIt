#!/usr/bin/env python3
"""Independent semantic-graph to quadratic-export verification.

Adapted from code/check_affine_export.py in the incoming
ConZFC_Shared_Pell_Bound_261_2026-10-24 package.  This version independently
checks every defining gate, replays the support-four nonnegative affine
substitutions, checks the exact dependency closure, and compares every
exported row.  No builder, exporter, optimizer, or upstream package is
imported.  Only Python's standard library is needed.

The mathematical equivalence being checked is finite: eliminated affine
gates have nonnegative integral restorations; unused free coordinates can
be zero, and unused definitional gates are then evaluated in source order.
The number-theoretic interpretation of the semantic graph is separate.
"""

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def read_polynomial(terms, nvars, location):
    require(isinstance(terms, list), location + ": terms must be a list")
    result = {}
    for term in terms:
        require(isinstance(term, list) and len(term) == 2, location + ": bad term")
        coefficient, monomial = term
        require(type(coefficient) is int, location + ": noninteger coefficient")
        require(isinstance(monomial, list), location + ": bad monomial")
        require(all(type(v) is int and 0 <= v < nvars for v in monomial),
                location + ": variable index outside domain")
        monomial = tuple(sorted(monomial))
        result[monomial] = result.get(monomial, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def dump(polynomial):
    return [[c, list(m)] for m, c in sorted(polynomial.items()) if c]


def multiply(left, right):
    result = {}
    for a, coefficient_a in left.items():
        for b, coefficient_b in right.items():
            key = tuple(sorted(a + b))
            result[key] = result.get(key, 0) + coefficient_a * coefficient_b
    return {m: c for m, c in result.items() if c}


def substitute_one(polynomial, variable, replacement):
    result = {}
    for monomial, coefficient in polynomial.items():
        term = {(): coefficient}
        for v in monomial:
            term = multiply(term, replacement if v == variable else {(v,): 1})
        for m, c in term.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def support(polynomial):
    return {v for m in polynomial for v in m}


def is_square_difference(polynomial):
    """Recognize exactly (x-y)^2, permitting x=y after collection."""
    if not polynomial:
        return True
    indices = sorted(support(polynomial))
    if len(indices) != 2:
        return False
    x, y = indices
    return polynomial == {(x, x): 1, (x, y): -2, (y, y): 1}


def validate_gate(polynomial, variable, location):
    require(polynomial.get((variable,)) == 1, location + ": gate is not monic")
    definition = {m: -c for m, c in polynomial.items() if m != (variable,)}
    require(all(all(v < variable for v in m) for m in definition),
            location + ": gate is not triangular")
    require(all(len(m) <= 2 for m in definition), location + ": nonquadratic gate")
    require(all(c >= 0 for c in definition.values()) or is_square_difference(definition),
            location + ": no supported proof of nonnegative gate restoration")
    return definition


def validate_quadratic_equation(equation, location):
    require(equation.get("schema") == "finite_quadratic_residuals_v1",
            location + ": unexpected schema")
    require(equation.get("domain") == "nonnegative integers", location + ": wrong domain")
    require(equation.get("polynomial") == "sum(square(row) for row in residuals)",
            location + ": wrong sum-of-squares convention")
    variables = equation["variables"]
    require(isinstance(variables, list), location + ": bad variable list")
    nvars = len(variables)
    rows = [read_polynomial(row["terms"], nvars, location + ":row:" + str(i))
            for i, row in enumerate(equation["residuals"])]
    require(all(p for p in rows), location + ": zero residual retained")
    require(all(len(m) <= 2 for p in rows for m in p), location + ": degree exceeds two")
    used = set().union(*(support(p) for p in rows)) if rows else set()
    require(used == set(range(nvars)), location + ": unused variable in final equation")
    require(equation["metrics"]["variables"] == nvars, location + ": variable count")
    require(equation["metrics"]["quadratic_rows"] == len(rows), location + ": row count")
    return rows


def verify(metadata, raw):
    raw_rows = validate_quadratic_equation(raw, "raw")
    variables = metadata["variables"]
    source_rows = metadata["rows"]
    nvars = len(variables)
    original = {i: read_polynomial(row["terms"], nvars, "source:" + str(i))
                for i, row in enumerate(source_rows)}
    require(all(len(m) <= 2 for p in original.values() for m in p),
            "source residual degree exceeds two")
    gates = {}
    for key, row_index in metadata["gates"].items():
        require(isinstance(key, str) and key.isdecimal() and str(int(key)) == key,
                "invalid gate-map key")
        variable = int(key)
        require(0 <= variable < nvars and type(row_index) is int and
                0 <= row_index < len(source_rows), "gate map outside domain")
        gates[variable] = row_index
    require(len(set(gates.values())) == len(gates), "multiple outputs share one gate row")
    require({i: row["gate"] for i, row in enumerate(source_rows) if row["gate"] is not None}
            == {j: v for v, j in gates.items()}, "gate map disagrees with all row annotations")
    gate_definitions = {v: validate_gate(original[j], v, "gate:" + str(v))
                        for v, j in gates.items()}

    # Replay substitutions in source variable order; keep definitions in source
    # coordinates.  The export policy tests the original row for affineness.
    rows = {i: dict(p) for i, p in original.items()}
    active = set(range(nvars))
    steps = []
    for variable in range(nvars):
        row_index = gates.get(variable)
        if row_index is None or any(len(m) > 1 for m in original[row_index]):
            continue
        require(row_index in rows, "definitional row already removed")
        polynomial = rows[row_index]
        require(polynomial.get((variable,)) == 1, "substituted affine gate not monic")
        definition = {m: -c for m, c in polynomial.items() if m != (variable,)}
        require(all(len(m) <= 1 and all(v < variable for v in m) for m in definition),
                "invalid affine restoration")
        require(all(c >= 0 for c in definition.values()), "negative affine restoration")
        require(support(definition) <= active, "restoration refers to an eliminated coordinate")
        if len(definition) > 4:
            continue
        steps.append({"row_original_index": row_index,
                      "variable_original_index": variable,
                      "variable_name": variables[variable]["name"],
                      "restoration": dump(definition)})
        del rows[row_index]
        active.remove(variable)
        for i in list(rows):
            if variable in support(rows[i]):
                rows[i] = substitute_one(rows[i], variable, definition)
        require(all(len(m) <= 2 for p in rows.values() for m in p),
                "affine substitution raised degree")

    rows = {i: p for i, p in rows.items() if p}
    remaining_gate_rows = {source_rows[i]["gate"]: i for i in rows
                           if source_rows[i]["gate"] is not None}
    required_rows = {i for i in rows if source_rows[i]["gate"] is None}
    required_variables = set().union(*(support(rows[i]) for i in required_rows))
    queue = list(required_variables)
    while queue:
        variable = queue.pop()
        row_index = remaining_gate_rows.get(variable)
        if row_index is None or row_index in required_rows:
            continue
        required_rows.add(row_index)
        new_variables = support(rows[row_index]) - required_variables
        queue.extend(new_variables)
        required_variables.update(new_variables)

    require(required_variables <= active, "dependency closure retained removed coordinates")
    ordered = sorted(required_variables)
    rename = {old: new for new, old in enumerate(ordered)}
    require([variables[i] for i in ordered] == raw["variables"],
            "exported variable list differs from dependency closure")
    expected = []
    for row_index in sorted(required_rows):
        polynomial = {tuple(rename[v] for v in m): c for m, c in rows[row_index].items()}
        expected.append({"label": source_rows[row_index]["label"], "terms": dump(polynomial)})
    require(expected == raw["residuals"],
            "exported residuals differ from exact substitution and dependency replay")
    require(len(steps) == raw["metrics"]["affine_gate_variables_eliminated"],
            "affine elimination count differs")
    unused = active - required_variables
    require(len(unused) == raw["metrics"]["unused_variables_removed"],
            "unused-coordinate count differs")
    require(metadata["wire_eliminated_source_sha256"] == raw["wire_eliminated_source_sha256"],
            "source binding differs")
    require(dict(Counter(v["kind"] for v in raw["variables"])) == raw["metrics"]["variable_kinds"],
            "variable-kind counts differ")

    certificate = {
        "schema": "nonnegative_affine_export_replay_v2",
        "metadata_sha256": digest(metadata), "raw_equation_sha256": digest(raw),
        "support_cap": 4, "steps": steps,
        "retained_original_indices_in_target_order": ordered,
        "surviving_source_rows_in_target_order": sorted(required_rows),
        "unused_original_coordinates": sorted(unused),
        "unused_free_coordinates_set_to_zero": sorted(unused - set(gates)),
        "unused_gate_definitions_in_source_order": [
            {"variable_original_index": v, "restoration": dump(gate_definitions[v])}
            for v in sorted(unused & set(gates))],
        "inverse": "Assign unused free coordinates zero; scan original variables in increasing order, "
                   "restoring each removed gate from its original nonnegative integer definition. "
                   "For the pure affine replay, reverse the elimination steps.",
    }
    receipt = {
        "verified": True, "original_variables": nvars, "original_rows": len(source_rows),
        "checked_defining_gates": len(gates), "nonnegative_affine_restorations": len(steps),
        "retained_variables": len(ordered), "retained_rows": len(expected),
        "unused_coordinates_removed": len(unused), "all_rows_compared": True,
        "all_exported_variables_occur": True,
        "maximum_exported_residual_degree": max(len(m) for p in raw_rows for m in p),
        "metadata_sha256": digest(metadata), "raw_equation_sha256": digest(raw),
        "independence": "No producer, optimizer, exporter, or upstream module imported.",
        "attribution": "Adapted from Shared_Pell_Bound_261 code/check_affine_export.py; "
                       "extended with complete gate and dependency-closure checks.",
    }
    return receipt, certificate


def check_expansion(raw, expanded):
    rows = validate_quadratic_equation(raw, "raw")
    total = {}
    for polynomial in rows:
        for monomial, coefficient in multiply(polynomial, polynomial).items():
            total[monomial] = total.get(monomial, 0) + coefficient
    total = {m: c for m, c in total.items() if c}
    require(expanded["domain"] == "nonnegative integers", "expanded domain differs")
    require(expanded["variables"] == len(raw["variables"]), "expanded variable count differs")
    require(dump(total) == expanded["terms"], "expanded polynomial differs from sum of squares")
    metrics = raw["metrics"]
    require(len(total) == metrics["expanded_monomials"], "expanded monomial count differs")
    require(max(map(len, total), default=0) == metrics["exact_degree"], "degree metric differs")
    require(max(map(abs, total.values()), default=0) == metrics["max_abs_expanded_coefficient"],
            "expanded height differs")
    return {"expanded_coefficients_checked": len(total), "expanded_sha256": digest(expanded)}


def negative_controls(metadata, raw, certificate):
    def rejected(mutated_metadata, mutated_raw, name):
        try:
            verify(mutated_metadata, mutated_raw)
        except (ValueError, KeyError, IndexError, TypeError):
            return name
        raise ValueError("corruption accepted: " + name)

    controls = []
    changed = deepcopy(raw)
    changed["residuals"][0]["terms"][0][0] += 1
    controls.append(rejected(metadata, changed, "changed_raw_coefficient"))
    changed = deepcopy(metadata)
    row_index = certificate["steps"][0]["row_original_index"]
    changed["rows"][row_index]["terms"][0][0] -= 1
    controls.append(rejected(changed, raw, "changed_affine_definition"))
    changed = deepcopy(raw)
    changed["variables"][0], changed["variables"][1] = changed["variables"][1], changed["variables"][0]
    controls.append(rejected(metadata, changed, "swapped_output_coordinates"))
    changed = deepcopy(metadata)
    first = min(changed["gates"], key=int)
    changed["gates"][first] = (changed["gates"][first] + 1) % len(changed["rows"])
    controls.append(rejected(changed, raw, "changed_gate_map"))
    changed = deepcopy(raw)
    changed["residuals"].pop()
    controls.append(rejected(metadata, changed, "removed_output_row"))
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metadata", type=Path)
    parser.add_argument("raw_equation", type=Path)
    parser.add_argument("--expanded", type=Path)
    parser.add_argument("--target", type=Path,
                        help="Also check target coordinate liveness and quadratic degree.")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    metadata = json.loads(args.metadata.read_text())
    raw = json.loads(args.raw_equation.read_text())
    receipt, certificate = verify(metadata, raw)
    receipt["negative_controls_rejected"] = negative_controls(metadata, raw, certificate)
    if args.expanded:
        receipt.update(check_expansion(raw, json.loads(args.expanded.read_text())))
    if args.target:
        target = json.loads(args.target.read_text())
        rows = validate_quadratic_equation(target, "contracted target")
        receipt["contracted_target_liveness"] = {
            "variables": len(target["variables"]), "rows": len(rows),
            "maximum_residual_degree": max(len(m) for p in rows for m in p),
            "all_variables_occur": True, "equation_sha256": digest(target)}
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    if args.certificate:
        args.certificate.write_text(json.dumps(certificate, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
