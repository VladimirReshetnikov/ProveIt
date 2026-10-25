#!/usr/bin/env python3
"""Materialize the finite ring/pairing theory for the frozen 240-variable P.

Python standard library only. No polynomial zero tests occur in this program.
The separate check.py does not import this module.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil
import tempfile


SCHEMA_DAG = "finite-theory.dag.v1"
SCHEMA_THEORY = "finite-theory.formulas.v1"
SCHEMA_METRICS = "finite-theory.metrics.v1"
SIGNATURE = [
    {"symbol": "0", "arity": 0}, {"symbol": "1", "arity": 0},
    {"symbol": "-", "arity": 1}, {"symbol": "L", "arity": 1},
    {"symbol": "R", "arity": 1}, {"symbol": "+", "arity": 2},
    {"symbol": "*", "arity": 2}, {"symbol": "pair", "arity": 2},
]


def fail_unless(condition, message):
    if not condition:
        raise ValueError(message)


def file_info(path):
    raw = path.read_bytes()
    return {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def dump(path, value, compact=False):
    text = json.dumps(value, sort_keys=True,
                      separators=(",", ":") if compact else None,
                      indent=None if compact else 2)
    path.write_text(text + "\n", encoding="utf-8")


class Circuit:
    """Hash-consed gates; sharing is allowed only in this arithmetic DAG."""

    def __init__(self, input_count):
        self.gates = []
        self.index = {}
        self.zero = self.gate("0")
        self.one = self.gate("1")
        self.inputs = [self.gate("input", input_index=i)
                       for i in range(input_count)]
        self.constants = {0: self.zero, 1: self.one}

    def gate(self, op, *args, input_index=None):
        if op in ("+", "*"):
            args = tuple(sorted(args))
        key = (op, input_index) if op == "input" else (op,) + tuple(args)
        if key in self.index:
            return self.index[key]
        j = len(self.gates)
        if op == "input":
            value = {"op": op, "index": input_index}
        elif op in ("0", "1"):
            value = {"op": op}
        else:
            value = {"op": op, "args": list(args)}
        self.gates.append(value)
        self.index[key] = j
        return j

    def constant(self, value):
        """Resolve every literal integer by binary doubling/add-one and minus."""
        if value in self.constants:
            return self.constants[value]
        if value < 0:
            gate = self.gate("-", self.constant(-value))
        else:
            half = self.constant(value // 2)
            gate = self.gate("+", half, half)
            if value & 1:
                gate = self.gate("+", gate, self.one)
        self.constants[value] = gate
        return gate

    def sum(self, gates):
        if not gates:
            return self.zero
        if len(gates) == 1:
            return gates[0]
        middle = len(gates) // 2
        return self.gate("+", self.sum(gates[:middle]), self.sum(gates[middle:]))

    def monomial(self, variables):
        if not variables:
            return self.one
        if len(variables) == 1:
            return self.inputs[variables[0]]
        middle = len(variables) // 2
        return self.gate("*", self.monomial(variables[:middle]),
                         self.monomial(variables[middle:]))

    def sparse_polynomial(self, terms):
        gates = []
        for coefficient, variables in terms:
            fail_unless(type(coefficient) is int and coefficient != 0,
                        "source polynomial requires nonzero integer coefficients")
            monomial = self.monomial(variables)
            if not variables:
                gate = self.constant(coefficient)
            elif coefficient == 1:
                gate = monomial
            elif coefficient == -1:
                gate = self.gate("-", monomial)
            else:
                gate = self.gate("*", self.constant(coefficient), monomial)
            gates.append(gate)
        return self.sum(gates)


def projection(index, variable, width):
    fail_unless(0 <= index < (1 << width), "projection index outside capacity")
    term = ["var", variable]
    for bit in range(width - 1, -1, -1):
        term = ["R" if (index >> bit) & 1 else "L", term]
    return term


def balanced_and(formulas):
    fail_unless(bool(formulas), "empty conjunction has no primitive syntax here")
    if len(formulas) == 1:
        return formulas[0]
    middle = len(formulas) // 2
    return ["and", balanced_and(formulas[:middle]), balanced_and(formulas[middle:])]


def universally(variables, formula):
    for variable in reversed(variables):
        formula = ["forall", variable, formula]
    return formula


def ring_pair_axioms():
    """Ten actual closed ASTs. No closure, numeral, or algebraic macros remain."""
    x, y, w = ["var", "x"], ["var", "y"], ["var", "w"]
    specifications = [
        ("ring_add_associativity", "xyw",
         ["=", ["+", ["+", x, y], w], ["+", x, ["+", y, w]]]),
        ("ring_add_commutativity", "xy", ["=", ["+", x, y], ["+", y, x]]),
        ("ring_add_zero", "x", ["=", ["+", x, ["0"]], x]),
        ("ring_add_inverse", "x", ["=", ["+", x, ["-", x]], ["0"]]),
        ("ring_mul_associativity", "xyw",
         ["=", ["*", ["*", x, y], w], ["*", x, ["*", y, w]]]),
        ("ring_mul_commutativity", "xy", ["=", ["*", x, y], ["*", y, x]]),
        ("ring_mul_one", "x", ["=", ["*", x, ["1"]], x]),
        ("ring_distributivity", "xyw",
         ["=", ["*", x, ["+", y, w]], ["+", ["*", x, y], ["*", x, w]]]),
        ("pair_left", "xy", ["=", ["L", ["pair", x, y]], x]),
        ("pair_right", "xy", ["=", ["R", ["pair", x, y]], y]),
    ]
    return [{"name": name, "formula": universally(variables, formula)}
            for name, variables, formula in specifications]


def make_theory(circuit, output, input_width, gate_width):
    def rho(gate):
        return projection(gate, "u", gate_width)

    equalities = []
    for j, gate in enumerate(circuit.gates):
        op = gate["op"]
        if op == "input":
            right = projection(gate["index"], "z", input_width)
        elif op in ("0", "1"):
            right = [op]
        else:
            right = [op] + [rho(k) for k in gate["args"]]
        equalities.append(["=", rho(j), right])
    clauses = equalities + [["not", ["=", rho(output), ["0"]]]]
    theta = ["forall", "z", ["exists", "u", balanced_and(clauses)]]
    return {
        "schema": SCHEMA_THEORY,
        "signature": SIGNATURE,
        "logical_symbols": ["=", "not", "and", "forall", "exists"],
        "sentences": ring_pair_axioms() + [{"name": "theta_P", "formula": theta}],
    }


def syntax_metrics(formula):
    """Count tree occurrences, including every repeated projection term."""
    count = Counter()
    maximum_term_depth = 0

    def term(node):
        nonlocal maximum_term_depth
        count["term_nodes"] += 1
        op = node[0]
        depth = 0 if op in ("var", "0", "1") else 1 + max(term(t) for t in node[1:])
        maximum_term_depth = max(maximum_term_depth, depth)
        return depth

    def visit(node):
        count["formula_nodes"] += 1
        op = node[0]
        if op == "=":
            return 1 + max(term(node[1]), term(node[2])), 0, 0
        if op in ("forall", "exists"):
            count["quantifier_nodes"] += 1
            sd, fd, qd = visit(node[2])
            return sd + 1, fd + 1, qd + 1
        children = [visit(child) for child in node[1:]]
        return (1 + max(t[0] for t in children),
                1 + max(t[1] for t in children), max(t[2] for t in children))

    syntax_depth, formula_depth, quantifier_depth = visit(formula)
    return {
        "syntax_nodes": count["term_nodes"] + count["formula_nodes"],
        "formula_nodes": count["formula_nodes"],
        "term_nodes": count["term_nodes"],
        "syntax_depth_edges": syntax_depth,
        "formula_depth_edges": formula_depth,
        "max_term_depth_edges": maximum_term_depth,
        "quantifier_nodes": count["quantifier_nodes"],
        "quantifier_depth": quantifier_depth,
    }


def build(equation_path, expanded_path, destination):
    equation = json.loads(equation_path.read_text(encoding="utf-8"))
    expanded = json.loads(expanded_path.read_text(encoding="utf-8"))
    fail_unless(equation["variables"] == expanded["variables"], "variable tables differ")
    fail_unless(equation["domain"] == expanded["domain"] == "unrestricted integers",
                "integer domain required")
    n = len(equation["variables"])
    circuit = Circuit(n)
    coefficients = {c for row in equation["residuals"] for c, _ in row["terms"]}
    for c in sorted(coefficients):
        circuit.constant(c)
    residual_gates = [circuit.sparse_polynomial(row["terms"])
                      for row in equation["residuals"]]
    summands = [circuit.gate("*", gate, gate) for gate in residual_gates]
    for i, j, sign in equation["gram_cross_terms"]:
        fail_unless(sign in (-1, 1), "cross-term sign must be plus or minus one")
        gate = circuit.gate("*", residual_gates[i], residual_gates[j])
        summands.append(circuit.gate("-", gate) if sign < 0 else gate)
    output = circuit.sum(summands)
    m = len(circuit.gates)
    r = (max(1, n) - 1).bit_length()
    s = (max(1, m) - 1).bit_length()
    destination.mkdir(parents=True, exist_ok=True)
    for source, name in [(equation_path, "source_equation.json"),
                         (expanded_path, "source_expanded_polynomial.json")]:
        target = destination / name
        if source.resolve() != target.resolve():
            shutil.copyfile(source, target)
    sources = {name: {"sha256": file_info(destination / name)["sha256"]}
               for name in ("source_equation.json", "source_expanded_polynomial.json")}
    dag = {
        "schema": SCHEMA_DAG, "input_count": n, "input_names": equation["variables"],
        "gates": circuit.gates, "output_gate": output,
        "residual_gates": residual_gates,
        "constants": {str(c): gate for c, gate in sorted(circuit.constants.items())},
        "source_files": sources,
    }
    theory = make_theory(circuit, output, r, s)
    dump(destination / "DAG.json", dag)
    dump(destination / "theory.json", theory, compact=True)
    sentence_metrics = {entry["name"]: syntax_metrics(entry["formula"])
                        for entry in theory["sentences"]}
    theory_metrics = {"sentence_count": len(sentence_metrics)}
    for key in next(iter(sentence_metrics.values())):
        values = [data[key] for data in sentence_metrics.values()]
        theory_metrics[key] = sum(values) if key.endswith("nodes") else max(values)
    depths = []
    for gate in circuit.gates:
        children = gate.get("args", [])
        depths.append(0 if not children else 1 + max(depths[k] for k in children))
    leaf_depths = []

    def conjunction_depths(count, depth=0):
        if count == 1:
            leaf_depths.append(depth)
        else:
            middle = count // 2
            conjunction_depths(middle, depth + 1)
            conjunction_depths(count - middle, depth + 1)

    conjunction_depths(m + 1)
    metrics = {
        "schema": SCHEMA_METRICS,
        "source": {
            "input_count": n, "residual_count": len(equation["residuals"]),
            "cross_term_count": len(equation["gram_cross_terms"]),
            "residual_term_count": sum(len(row["terms"]) for row in equation["residuals"]),
            "expanded_monomial_count": len(expanded["terms"]),
            "expanded_degree": max(len(mono) for _, mono in expanded["terms"]),
            "expanded_coefficient_height": max(abs(c) for c, _ in expanded["terms"]),
        },
        "dag": {
            "gate_count": m, "operation_counts": dict(sorted(Counter(
                gate["op"] for gate in circuit.gates).items())),
            "output_gate": output, "maximum_gate_depth_edges": max(depths),
            "output_gate_depth_edges": depths[output],
            "input_projection_depth_edges": r, "input_leaf_capacity": 1 << r,
            "gate_projection_depth_edges": s, "gate_leaf_capacity": 1 << s,
        },
        "sentences": sentence_metrics,
        "theory": theory_metrics,
        "theta_conjunction": {
            "leaf_count": m + 1, "and_nodes": m,
            "max_conjunction_depth_edges": max(leaf_depths),
            "min_conjunction_depth_edges": min(leaf_depths),
        },
        "files": {name: file_info(destination / name) for name in
                  ("DAG.json", "theory.json", "source_equation.json",
                   "source_expanded_polynomial.json")},
    }
    dump(destination / "metrics.json", metrics)
    return metrics


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--equation", type=Path, default=here / "source_equation.json")
    parser.add_argument("--expanded", type=Path,
                        default=here / "source_expanded_polynomial.json")
    parser.add_argument("--out", type=Path, default=here)
    parser.add_argument("--check", action="store_true",
                        help="rebuild in temporary storage and require byte-identical artifacts")
    args = parser.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix="finite-theory-check-") as temporary:
            rebuilt = Path(temporary)
            metrics = build(args.equation, args.expanded, rebuilt)
            for name in ("DAG.json", "theory.json", "metrics.json", "source_equation.json",
                         "source_expanded_polynomial.json"):
                fail_unless((rebuilt / name).read_bytes() == (args.out / name).read_bytes(),
                            "reproducibility failure: " + name)
        print("PASS: all five materialized JSON files reproduce byte for byte")
    else:
        metrics = build(args.equation, args.expanded, args.out)
        print("Wrote the arithmetic DAG, eleven closed ASTs, sources, and exact metrics")
    print(json.dumps({"dag": metrics["dag"], "theta_P": metrics["sentences"]["theta_P"],
                      "theory": metrics["theory"]}, indent=2))


if __name__ == "__main__":
    main()
