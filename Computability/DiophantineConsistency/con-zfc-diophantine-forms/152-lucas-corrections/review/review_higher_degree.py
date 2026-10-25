#!/usr/bin/env python3
"""Third implementation: audit frozen higher-degree circuits without expansion.

Imports no builder or verifier from the reviewed package.  Sparse expansion
is confined to local blocks over independent source-coordinate registers.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import json
import math


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cleaned(poly):
    return {monomial: coefficient for monomial, coefficient in poly.items() if coefficient}


def plus(first, second, sign=1):
    result = defaultdict(int, first)
    for monomial, coefficient in second.items():
        result[monomial] += sign * coefficient
    return cleaned(result)


def times(first, second):
    result = defaultdict(int)
    for left, a in first.items():
        for right, b in second.items():
            result[tuple(sorted(left + right))] += a * b
    return cleaned(result)


def source_polynomial(row):
    result = defaultdict(int)
    for coefficient, variables in row["terms"]:
        need(type(coefficient) is int, "noninteger source coefficient")
        result[tuple(sorted(variables))] += coefficient
    return cleaned(result)


def local_identity(nodes, block, allowed):
    start, end = block["start"], block["root"]
    local = {}
    for position in range(start, end + 1):
        node = nodes[position]
        if node[0] == "const":
            need(len(node) == 2 and type(node[1]) is int, "bad constant")
            local[position] = {} if node[1] == 0 else {(): node[1]}
            continue
        need(node[0] in ("+", "-", "*") and len(node) == 3, "nonpolynomial node")
        operands = []
        for pointer in node[1:]:
            need(type(pointer) is int and 0 <= pointer < position, "circuit cycle")
            if pointer >= start:
                operands.append(local[pointer])
            else:
                need(pointer in allowed, "unbound external block reference")
                operands.append({(allowed[pointer],): 1})
        a, b = operands
        local[position] = times(a, b) if node[0] == "*" else plus(a, b, -1 if node[0] == "-" else 1)
    return local[end]


def forward_gradient(program, modulus):
    n = len(program["variables"])
    values, derivatives = [], []
    for node in program["nodes"]:
        op = node[0]
        if op == "var":
            value, derivative = node[1] + 3, [0] * n
            derivative[node[1]] = 1
        elif op == "const":
            value, derivative = node[1], [0] * n
        else:
            a, b = node[1:]
            if op == "*":
                value = values[a] * values[b]
                derivative = [(derivatives[a][j] * values[b] + derivatives[b][j] * values[a]) % modulus for j in range(n)]
            else:
                sign = -1 if op == "-" else 1
                value = values[a] + sign * values[b]
                derivative = [(derivatives[a][j] + sign * derivatives[b][j]) % modulus for j in range(n)]
        values.append(value % modulus)
        derivatives.append(derivative)
    return derivatives[program["output"]]


def profile_audit(source, source_hash, program, pivot_certificate, dependency):
    need(source["domain"] == program["domain"] == "unrestricted integers", "integer domain binding")
    need(program["source_sha256"] == pivot_certificate["source_sha256"] == source_hash, "profile source binding")
    rows, n = source["residuals"], len(source["variables"])
    inputs, nodes = program["retained_source_indices"], program["nodes"]
    need(inputs == sorted(set(inputs)) and all(type(i) is int and 0 <= i < n for i in inputs), "input map")
    need(nodes[:len(inputs)] == [["var", j] for j in range(len(inputs))], "input leaf map")
    need(program["variables"] == [{"source_index": j, **source["variables"][j]} for j in inputs], "coordinate metadata")
    degree = {j: 1 for j in inputs}
    l1 = {j: 1 for j in inputs}
    lead = {j: j + 3 for j in inputs}
    wires = {position: source_index for position, source_index in enumerate(inputs)}
    assigned = set(inputs)
    used_rows, pivots = set(), []
    residuals, residual_info = [], []
    cursor, modulus, residual_phase = len(inputs), 1000000007, False
    for number, block in enumerate(program["blocks"]):
        need(block["start"] == cursor and cursor <= block["root"] < len(nodes), "block coverage")
        if block["kind"] == "sum_of_squares":
            need(number == len(program["blocks"]) - 1 and residual_phase, "SOS placement")
            actual = local_identity(nodes, block, {root: j for j, root in enumerate(residuals)})
            need(actual == {(j, j): 1 for j in range(len(residuals))}, "SOS identity")
            need(block["root"] == program["output"] == len(nodes) - 1, "output binding")
            cursor = block["root"] + 1
            continue
        row_id = block["source_row"]
        need(type(row_id) is int and 0 <= row_id < len(rows) and row_id not in used_rows, "row partition")
        expected = source_polynomial(rows[row_id])
        used_rows.add(row_id)
        if block["kind"] == "definition":
            need(not residual_phase, "late definition")
            variable = block["variable"]
            need(variable not in assigned and 0 <= variable < n, "duplicate coordinate definition")
            coefficient = expected.pop((variable,), 0)
            need(coefficient in (-1, 1), "nonunit pivot")
            need(all(variable not in monomial for monomial in expected), "recursive pivot")
            expected = {monomial: -coefficient * value for monomial, value in expected.items()}
            pivots.append((row_id, variable))
        else:
            need(block["kind"] == "residual", "unknown block")
            residual_phase = True
        need(all(j in assigned for monomial in expected for j in monomial), "non-topological source dependency")
        need(local_identity(nodes, block, wires) == expected, "local polynomial identity")
        d = max((sum(degree[j] for j in monomial) for monomial in expected), default=0)
        bound = sum(abs(value) * math.prod(l1[j] for j in monomial) for monomial, value in expected.items())
        value = sum(coefficient * math.prod(lead[j] for j in monomial) for monomial, coefficient in expected.items()
                    if sum(degree[j] for j in monomial) == d) % modulus
        if block["kind"] == "definition":
            assigned.add(variable)
            degree[variable], l1[variable], lead[variable] = d, bound, value
            wires[block["root"]] = variable
        else:
            residuals.append(block["root"])
            residual_info.append((row_id, d, bound, value))
        cursor = block["root"] + 1
    need(cursor == len(nodes), "trailing circuit data")
    need(assigned == set(range(n)), "coordinate partition")
    need(used_rows == set(range(len(rows))), "residual partition")
    need(residuals == program["residual_roots"], "remaining roots")
    certificate_pivots = [(s["row"], s["variable"]) for s in pivot_certificate["steps"]]
    need(len(certificate_pivots) == len(set(certificate_pivots)) == len(pivots), "pivot certificate census")
    need(set(certificate_pivots) == set(pivots), "pivot certificate/program agreement")
    cert = program["degree_certificate"]
    need(cert["source_variable_degrees"] == [degree[j] for j in range(n)], "degree bounds")
    need(cert["retained_source_rows"] == [r for r, _, _, _ in residual_info], "degree row map")
    need(cert["residual_degrees"] == [d for _, d, _, _ in residual_info], "residual degree bounds")
    need(cert["modulus"] == modulus and cert["input_direction"] == "source_index + 3", "homogeneous witness convention")
    d_max = max(d for _, d, _, _ in residual_info)
    witness = next(info for info in residual_info if info[0] == cert["witness_source_row"])
    need(witness[1] == d_max and witness[3] == cert["witness_top_residue"] != 0, "leading homogeneous nonvanishing")
    height_bound = sum(bound * bound for _, _, bound, _ in residual_info)
    height_bits = height_bound.bit_length()
    need(program["metrics"]["variables"] == len(inputs), "variable metric")
    need(program["metrics"]["residuals"] == len(residuals), "residual metric")
    need(program["metrics"]["eliminated_variables"] == len(pivots), "elimination metric")
    need(program["metrics"]["degree"] == 2 * d_max, "exact degree metric")
    need(program["metrics"]["coefficient_height_strict_power_of_two"] == height_bits, "height metric")
    gradient = forward_gradient(program, modulus)
    need(all(gradient), "nonzero partial derivative witness")
    need(dependency["variables"] == len(inputs) and dependency["modulus"] == modulus, "dependency metadata")
    need(dependency["witnesses"] == [{"input_direction": "index + 3", "derivatives": [[j, value] for j, value in enumerate(gradient)]}], "independent forward/reverse derivative agreement")
    return {"variables": len(inputs), "unit_pivots": len(pivots), "remaining_residuals": len(residuals),
            "degree": 2 * d_max, "height_strict_power_of_two": height_bits,
            "height_bound_sha256_unsigned_big_endian": hashlib.sha256(height_bound.to_bytes((height_bits + 7) // 8, "big")).hexdigest(),
            "witness_source_row": witness[0], "witness_top_residue": witness[3],
            "modulus": modulus, "source_partition": "PASS", "local_identities": "PASS",
            "topological_restoration": "PASS", "all_inputs_essential": True}


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release", type=Path, default=here.parent / "alternative/composed_release")
    parser.add_argument("--frozen-source", type=Path, default=here / "release/equations/integer248/equation.json")
    parser.add_argument("--output", type=Path, default=here / "HIGHER_DEGREE_INDEPENDENT_REVIEW.json")
    args = parser.parse_args()
    source_path = args.release / "source/equation248.json"
    need(source_path.read_bytes() == args.frozen_source.read_bytes(), "frozen quartic source bytes differ")
    source_hash = sha(source_path)
    need(source_hash == "c51ebc12534db042bd1c7bf7c59f84602f51625e2d952dffa82fa054b5d92192", "published frozen source digest")
    source = json.loads(source_path.read_text())
    need(source["domain"] == "unrestricted integers" and len(source["variables"]) == 248 and len(source["residuals"]) == 182, "source census")
    need(json.loads((args.release / "SOURCE.json").read_text())["source_sha256"] == source_hash, "source provenance metadata")
    dependencies = {entry["equation"]: entry for entry in json.loads((args.release / "DEPENDENCY_CERTIFICATES.json").read_text())}
    profiles, hashes = {}, {"source/equation248.json": source_hash}
    files = sorted((args.release / "equations").glob("*.json"))
    need(len(files) == 8, "profile census")
    for path in files:
        certificate_path = args.release / "certificates" / path.name
        program = json.loads(path.read_text())
        cert = json.loads(certificate_path.read_text())
        profiles[path.stem] = profile_audit(source, source_hash, program, cert, dependencies[path.name])
        hashes[str(path.relative_to(args.release))] = sha(path)
        hashes[str(certificate_path.relative_to(args.release))] = sha(certificate_path)
    for name in ("SOURCE.json", "DEPENDENCY_CERTIFICATES.json", "section.tex", "verify.py", "build.py", "expand_octic.py"):
        hashes[name] = sha(args.release / name)
    receipt = {"verdict": "PASS", "reviewer": "direct_quartic independent agent",
        "scope": "Unit-pivot integer zero-set bijections, exact circuit/source identities, degree nonvanishing, L1 coefficient-height bounds, source248 binding, and variable essentiality; no repeated complete octic expansion.",
        "source_sha256": source_hash, "source_byte_identity": True, "profiles": profiles,
        "reviewed_files_sha256": hashes, "audit_script_sha256": sha(Path(__file__)),
        "imports_from_reviewed_package": [], "complete_higher_degree_expansion_performed": False}
    review_markdown = args.output.with_suffix(".md")
    if review_markdown.exists():
        receipt["review_markdown_sha256"] = sha(review_markdown)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"verdict": "PASS", "profiles": profiles, "source_sha256": source_hash}, indent=2))


if __name__ == "__main__":
    main()
