#!/usr/bin/env python3
"""Independent exact check of a signed-DAG quartic artifact.

No builder module is imported. Gate equations are read from the delivered
residual list and matched to the literal DAG, then their squares are
expanded independently and compared term for term with the final file.
"""
import argparse
import collections
import hashlib
import json
import pathlib


def ring_add(left, right, sign=1):
    result = dict(left)
    for powers, value in right.items():
        result[powers] = result.get(powers, 0) + sign * value
        if not result[powers]:
            del result[powers]
    return result


def ring_multiply(left, right):
    result = collections.defaultdict(int)
    for powers1, value1 in left.items():
        for powers2, value2 in right.items():
            result[tuple(sorted(powers1 + powers2))] += value1 * value2
    return {powers: value for powers, value in result.items() if value}


def decode(terms):
    result = {}
    for coefficient, monomial in terms:
        powers = tuple(monomial)
        if powers != tuple(sorted(powers)) or not coefficient or powers in result:
            raise ValueError("Noncanonical sparse polynomial")
        result[powers] = coefficient
    return result


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(folder):
    circuit = json.loads((folder / "circuit_integer.json").read_text())
    rows = json.loads((folder / "residuals_integer.json").read_text())
    equation = json.loads((folder / "equation_integer.json").read_text())
    claimed = json.loads((folder / "summary_integer.json").read_text())
    ninputs = len(circuit["variable_names"])
    gate_rows = {}
    other_rows = []
    guarded_rows = []
    for row in rows:
        if row["label"].startswith("nonlinear gate "):
            index = int(row["label"].split()[-1])
            kind = "nonlinear"
        elif row["label"].startswith("affine support barrier "):
            index = int(row["label"].split()[-1])
            kind = "affine"
        elif row["label"].startswith("semantic nonnegativity "):
            guarded_rows.append(row)
            continue
        else:
            other_rows.append(row)
            continue
        require(index not in gate_rows, "Repeated gate residual")
        gate_rows[index] = kind, decode(row["terms"])

    forms = []
    nextvar = ninputs
    nonlinear = affine = 0
    for index, node in enumerate(circuit["nodes"]):
        kind = node[0]
        require(kind in ("c", "v", "a", "s", "m"), "Unknown DAG operator")
        if kind == "c":
            value = {(): node[1]} if node[1] else {}
        elif kind == "v":
            require(0 <= node[1] < ninputs, "Input index outside interface")
            value = {(node[1],): 1}
        else:
            require(0 <= node[1] < index and 0 <= node[2] < index, "Nontopological DAG")
            if kind == "m":
                value = ring_multiply(forms[node[1]], forms[node[2]])
            else:
                value = ring_add(forms[node[1]], forms[node[2]], 1 if kind == "a" else -1)
        if index in gate_rows:
            rowkind, actual = gate_rows[index]
            wire = {(nextvar,): 1}
            expected = ring_add(wire, value, -1)
            require(expected == actual, "Gate residual does not match DAG at node " + str(index))
            require(max(map(len, value), default=0) <= 2, "Gate is not quadratic")
            if rowkind == "nonlinear":
                require(kind == "m" and max(map(len, value), default=0) == 2, "Nonlinear gate classification")
                nonlinear += 1
            else:
                require(max(map(len, value), default=0) <= 1, "Affine barrier is not affine")
                affine += 1
            value = wire
            nextvar += 1
        require(max(map(len, value), default=0) <= 1, "Unretained nonlinear gate")
        forms.append(value)

    require(len(other_rows) == len(circuit["equalities"]), "Final equality count mismatch")
    for row, (left, right, label) in zip(other_rows, circuit["equalities"]):
        require(row["label"] == label, "Final equality order mismatch")
        expected = ring_add(forms[left], forms[right], -1)
        require(expected == decode(row["terms"]), "Final equality transcription mismatch")

    require(len(guarded_rows) == len(circuit["nonnegative_inputs"]), "Guard count mismatch")
    require(set(circuit["nonnegative_inputs"]).isdisjoint(circuit["unrestricted_inputs"]), "Overlapping domains")
    require(set(circuit["nonnegative_inputs"]) | set(circuit["unrestricted_inputs"]) == set(range(ninputs)), "Incomplete input domains")
    for row, index in zip(guarded_rows, circuit["nonnegative_inputs"]):
        require(row["label"] == "semantic nonnegativity " + str(index), "Guard coordinate mismatch")
        a, b, c = nextvar, nextvar + 1, nextvar + 2
        expected = {(index,): 1, (a, a): -1, (b, b): -1, (c, c): -1, (c,): -1}
        require(expected == decode(row["terms"]), "Three-square guard mismatch")
        nextvar += 3

    polynomial = collections.defaultdict(int)
    for row in rows:
        value = decode(row["terms"])
        for powers, coefficient in ring_multiply(value, value).items():
            polynomial[powers] += coefficient
    polynomial = {p: v for p, v in polynomial.items() if v}
    actual = decode(equation["terms"])
    require(polynomial == actual, "Expanded equation differs from sum of squared residuals")
    require(equation["domain"] == "unrestricted integers", "Wrong polynomial domain")
    require(equation["variable_count"] == nextvar, "Variable count mismatch")
    require({j for powers in actual for j in powers} == set(range(nextvar)), "Nonlive variable")
    degree = max(map(len, actual))
    require(degree == 4, "Polynomial is not exactly quartic")
    require(claimed["ordinary_polynomial_variables"] == nextvar, "Claimed variable count")
    require(claimed["ordinary_polynomial_monomials"] == len(actual), "Claimed term count")
    require(claimed["nonlinear_wires"] == nonlinear, "Claimed nonlinear count")
    require(claimed["retained_affine_wires"] == affine, "Claimed affine count")
    maximum = max(abs(x) for x in actual.values())
    require(claimed["max_abs_coefficient"] == maximum, "Claimed coefficient height")
    return {
        "status": "PASS",
        "method": "Independent exact sparse-ring reconstruction; no builder imports",
        "variables": nextvar,
        "degree": degree,
        "monomials": len(actual),
        "quadratic_residuals": len(rows),
        "nonlinear_wires": nonlinear,
        "affine_barriers": affine,
        "max_abs_coefficient": maximum,
        "sha256": {name: hashlib.sha256((folder / name).read_bytes()).hexdigest()
                   for name in ["circuit_integer.json", "residuals_integer.json", "equation_integer.json", "summary_integer.json"]},
        "scope": "Exact artifact, degree and count audit; mathematical source and calibration are separate proofs",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("folder", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    result = check(args.folder)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
