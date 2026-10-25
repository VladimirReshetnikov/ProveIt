#!/usr/bin/env python3
"""Independently check the complete finite functional theory, using only stdlib.

This program does not import the builder and does not test polynomial values at
sample points.  It expands coefficients exactly, checks the actual formula tree,
and recomputes every recorded size/depth measurement.  It checks a finite source
construction, not a formal proof of ZFC's consistency or a new Diophantine
compilation.  Python -O does not disable any check.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


class CheckError(Exception):
    """A supplied artifact does not meet its claimed invariant."""


def require(condition, message):
    if not condition:
        raise CheckError(message)


SOURCE_SHA256 = {
    "source_equation.json":
        "d293792cd1eee936256d74d6171294bd37bcbc4b577b8abc3347b97c7d5beace",
    "source_expanded_polynomial.json":
        "2d0d436fb8c59c4aaf3954b25398e27944a75ede6a94c448f72a6aa014940d18",
}

SIGNATURE = [
    {"symbol": "0", "arity": 0}, {"symbol": "1", "arity": 0},
    {"symbol": "-", "arity": 1}, {"symbol": "L", "arity": 1},
    {"symbol": "R", "arity": 1}, {"symbol": "+", "arity": 2},
    {"symbol": "*", "arity": 2}, {"symbol": "pair", "arity": 2},
]
FUNCTION_ARITY = {entry["symbol"]: entry["arity"] for entry in SIGNATURE}
SENTENCE_NAMES = [
    "ring_add_associativity", "ring_add_commutativity", "ring_add_zero",
    "ring_add_inverse", "ring_mul_associativity", "ring_mul_commutativity",
    "ring_mul_one", "ring_distributivity", "pair_left", "pair_right",
    "theta_P",
]
COUNT_METRICS = {"syntax_nodes", "formula_nodes", "term_nodes", "quantifier_nodes"}
DEPTH_METRICS = {
    "syntax_depth_edges", "formula_depth_edges", "max_term_depth_edges",
    "quantifier_depth",
}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "JSON object has duplicate key: " + str(key))
        result[key] = value
    return result


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def file_record(path):
    content = path.read_bytes()
    return {"sha256": hashlib.sha256(content).hexdigest(), "bytes": len(content)}


def checked_int(value, message):
    require(type(value) is int, message)
    return value


def load_sparse(terms, variable_count, label):
    require(isinstance(terms, list), label + ": terms must be a list")
    result = {}
    for index, item in enumerate(terms):
        where = label + ": term " + str(index)
        require(isinstance(item, list) and len(item) == 2, where + ": bad pair")
        coefficient, monomial = item
        checked_int(coefficient, where + ": coefficient is not an integer")
        require(coefficient != 0, where + ": zero coefficient is not collected")
        require(isinstance(monomial, list), where + ": bad monomial")
        for variable in monomial:
            checked_int(variable, where + ": variable is not an integer")
            require(0 <= variable < variable_count, where + ": variable out of range")
        require(monomial == sorted(monomial), where + ": monomial not sorted")
        key = tuple(monomial)
        require(key not in result, where + ": repeated monomial")
        result[key] = coefficient
    return result


def add_poly(left, right):
    result = dict(left)
    for monomial, coefficient in right.items():
        value = result.get(monomial, 0) + coefficient
        if value:
            result[monomial] = value
        else:
            result.pop(monomial, None)
    return result


def neg_poly(poly):
    return {monomial: -coefficient for monomial, coefficient in poly.items()}


def mul_poly(left, right):
    result = {}
    for a, coefficient_a in left.items():
        for b, coefficient_b in right.items():
            monomial = tuple(sorted(a + b))
            result[monomial] = result.get(monomial, 0) + coefficient_a * coefficient_b
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


def polynomial_degree(poly):
    return max((len(monomial) for monomial in poly), default=0)


def expect_equal_polynomials(actual, expected, label):
    if actual == expected:
        return
    for monomial in sorted(set(actual) | set(expected)):
        if actual.get(monomial, 0) != expected.get(monomial, 0):
            raise CheckError(
                label + ": coefficient mismatch at " + str(monomial)
                + "; got " + str(actual.get(monomial, 0))
                + ", expected " + str(expected.get(monomial, 0))
            )
    raise CheckError(label + ": polynomial mismatch")


def verify_sources(folder, dag):
    for name, expected in SOURCE_SHA256.items():
        actual = file_record(folder / name)["sha256"]
        require(actual == expected, name + ": does not match the supplied frozen input")
        require(dag["source_files"].get(name) == {"sha256": actual},
                "DAG source binding mismatch for " + name)
    require(set(dag["source_files"]) == set(SOURCE_SHA256), "unexpected DAG source file")
    source = load_json(folder / "source_equation.json")
    expanded = load_json(folder / "source_expanded_polynomial.json")
    require(source["schema"] == "proveit.diophantine.gram.v1", "bad Gram source schema")
    require(expanded["schema"] == "proveit.diophantine.sparse.v1", "bad expansion schema")
    require(source["domain"] == expanded["domain"] == "unrestricted integers",
            "source domain is not unrestricted integers")
    require(len(source["variables"]) == 240, "expected 240 input coordinates")
    require(source["variables"] == expanded["variables"], "source coordinate names differ")
    require(dag["input_count"] == 240, "DAG input count differs")
    require(dag["input_names"] == source["variables"], "DAG input names differ")
    require(len(source["residuals"]) == 177, "expected 177 residuals")
    require(len(source["gram_cross_terms"]) == 13, "expected 13 signed cross terms")
    residuals = [load_sparse(item["terms"], 240, "residual " + str(index))
                 for index, item in enumerate(source["residuals"])]
    require(all(polynomial_degree(poly) <= 2 for poly in residuals),
            "a source residual is not quadratic")
    target = load_sparse(expanded["terms"], 240, "complete source expansion")
    require(len(target) == 5803, "expected all 5803 collected coefficients")
    require(polynomial_degree(target) == 4, "complete source degree is not four")
    require({i for monomial in target for i in monomial} == set(range(240)),
            "complete polynomial does not use all 240 coordinates")
    result = {}
    for poly in residuals:
        result = add_poly(result, mul_poly(poly, poly))
    for index, item in enumerate(source["gram_cross_terms"]):
        require(isinstance(item, list) and len(item) == 3, "bad signed Gram edge")
        i, j, sign = item
        for value in item:
            checked_int(value, "noninteger Gram edge entry")
        require(0 <= i < len(residuals) and 0 <= j < len(residuals),
                "Gram residual index out of range")
        require(i != j and sign in (-1, 1), "bad signed Gram edge")
        contribution = mul_poly(residuals[i], residuals[j])
        result = add_poly(result, contribution if sign == 1 else neg_poly(contribution))
    expect_equal_polynomials(result, target, "independent residual/Gram expansion")
    source_metrics = {
        "input_count": 240,
        "residual_count": len(residuals),
        "cross_term_count": len(source["gram_cross_terms"]),
        "residual_term_count": sum(len(poly) for poly in residuals),
        "expanded_monomial_count": len(target),
        "expanded_degree": polynomial_degree(target),
        "expanded_coefficient_height": max(abs(c) for c in target.values()),
    }
    return source, residuals, target, source_metrics


def projection_depth(count):
    return (max(1, count) - 1).bit_length()


def verify_binary_constant(gates, index, value, checked):
    pair = (index, value)
    if pair in checked:
        return
    gate = gates[index]
    if value in (0, 1):
        require(gate == {"op": str(value)}, "constant base is not literal 0 or 1")
    elif value < 0:
        require(gate["op"] == "-", "negative constant is not unary negation")
        verify_binary_constant(gates, gate["args"][0], -value, checked)
    elif value % 2 == 0:
        require(gate["op"] == "+" and gate["args"][0] == gate["args"][1],
                "even constant is not a binary doubling")
        verify_binary_constant(gates, gate["args"][0], value // 2, checked)
    else:
        require(gate["op"] == "+", "odd constant is not an addition")
        a, b = gate["args"]
        if gates[a] == {"op": "1"}:
            verify_binary_constant(gates, b, value - 1, checked)
        elif gates[b] == {"op": "1"}:
            verify_binary_constant(gates, a, value - 1, checked)
        else:
            raise CheckError("odd constant is not binary doubling plus one")
    checked.add(pair)


def verify_dag(dag, source, residuals, target):
    require(dag["schema"] == "finite-theory.dag.v1", "bad arithmetic DAG schema")
    gates = dag["gates"]
    require(isinstance(gates, list) and gates, "DAG has no gates")
    polynomial_values, depths, input_indices = [], [], []
    operation_counts = Counter()
    for index, gate in enumerate(gates):
        require(isinstance(gate, dict), "gate is not an object")
        op = gate.get("op")
        require(op in ("0", "1", "input", "-", "+", "*"), "unknown gate operation")
        operation_counts[op] += 1
        if op in ("0", "1"):
            require(set(gate) == {"op"}, "literal gate has unexpected fields")
            value = {} if op == "0" else {(): 1}
            depth = 0
        elif op == "input":
            require(set(gate) == {"op", "index"}, "input gate has unexpected fields")
            coordinate = checked_int(gate["index"], "noninteger input index")
            require(0 <= coordinate < 240, "input coordinate out of range")
            input_indices.append(coordinate)
            value, depth = {(coordinate,): 1}, 0
        else:
            require(set(gate) == {"op", "args"}, "arithmetic gate has unexpected fields")
            args = gate["args"]
            require(isinstance(args, list) and len(args) == (1 if op == "-" else 2),
                    "arithmetic gate has wrong arity")
            for argument in args:
                checked_int(argument, "noninteger gate reference")
                require(0 <= argument < index, "DAG reference is not topological")
            depth = 1 + max(depths[argument] for argument in args)
            if op == "-":
                value = neg_poly(polynomial_values[args[0]])
            elif op == "+":
                value = add_poly(polynomial_values[args[0]], polynomial_values[args[1]])
            else:
                value = mul_poly(polynomial_values[args[0]], polynomial_values[args[1]])
        require(polynomial_degree(value) <= 4, "a DAG gate has degree greater than four")
        polynomial_values.append(value)
        depths.append(depth)
    require(sorted(input_indices) == list(range(240)),
            "DAG does not have exactly one gate for every input coordinate")
    output = checked_int(dag["output_gate"], "noninteger output gate")
    require(0 <= output < len(gates), "output gate out of range")
    expect_equal_polynomials(polynomial_values[output], target, "complete DAG expansion")
    require(len(dag["residual_gates"]) == len(residuals), "wrong residual-gate count")
    for i, gate_id in enumerate(dag["residual_gates"]):
        checked_int(gate_id, "noninteger residual-gate reference")
        require(0 <= gate_id < len(gates), "residual gate out of range")
        expect_equal_polynomials(polynomial_values[gate_id], residuals[i],
                                 "residual gate " + str(i))
    require(isinstance(dag["constants"], dict), "constant table is not an object")
    required_constants = {0, 1} | {c for poly in residuals for c in poly.values()}
    declared_constants = set()
    checked = set()
    for decimal, gate_id in dag["constants"].items():
        try:
            value = int(decimal)
        except (TypeError, ValueError) as error:
            raise CheckError("invalid constant decimal") from error
        require(str(value) == decimal, "constant decimal is not canonical")
        declared_constants.add(value)
        checked_int(gate_id, "noninteger constant-gate reference")
        require(0 <= gate_id < len(gates), "constant gate out of range")
        expected = {(): value} if value else {}
        expect_equal_polynomials(polynomial_values[gate_id], expected,
                                 "constant " + decimal)
        verify_binary_constant(gates, gate_id, value, checked)
    require(required_constants <= declared_constants,
            "constant table omits a supplied coefficient or 0/1")
    r, s = projection_depth(240), projection_depth(len(gates))
    return {
        "gate_count": len(gates),
        "operation_counts": dict(sorted(operation_counts.items())),
        "output_gate": output,
        "maximum_gate_depth_edges": max(depths),
        "output_gate_depth_edges": depths[output],
        "input_projection_depth_edges": r,
        "input_leaf_capacity": 1 << r,
        "gate_projection_depth_edges": s,
        "gate_leaf_capacity": 1 << s,
    }


def projection(variable, index, width):
    term = ["var", variable]
    for bit_position in range(width - 1, -1, -1):
        term = ["R" if ((index >> bit_position) & 1) else "L", term]
    return term


def quantify(names, body):
    for name in reversed(names):
        body = ["forall", name, body]
    return body


def ring_and_pair_axioms():
    x, y, w = ["var", "x"], ["var", "y"], ["var", "w"]
    return [
        quantify(["x", "y", "w"],
                 ["=", ["+", ["+", x, y], w], ["+", x, ["+", y, w]]]),
        quantify(["x", "y"], ["=", ["+", x, y], ["+", y, x]]),
        quantify(["x"], ["=", ["+", x, ["0"]], x]),
        quantify(["x"], ["=", ["+", x, ["-", x]], ["0"]]),
        quantify(["x", "y", "w"],
                 ["=", ["*", ["*", x, y], w], ["*", x, ["*", y, w]]]),
        quantify(["x", "y"], ["=", ["*", x, y], ["*", y, x]]),
        quantify(["x"], ["=", ["*", x, ["1"]], x]),
        quantify(["x", "y", "w"],
                 ["=", ["*", x, ["+", y, w]],
                  ["+", ["*", x, y], ["*", x, w]]]),
        quantify(["x", "y"], ["=", ["L", ["pair", x, y]], x]),
        quantify(["x", "y"], ["=", ["R", ["pair", x, y]], y]),
    ]


def term_metrics(term, bound):
    require(isinstance(term, list) and term and isinstance(term[0], str),
            "malformed term node")
    op = term[0]
    if op == "var":
        require(len(term) == 2 and isinstance(term[1], str), "bad variable node")
        require(term[1] in bound, "free variable: " + term[1])
        return 1, 0
    require(op in FUNCTION_ARITY, "term uses an undeclared function")
    require(len(term) == FUNCTION_ARITY[op] + 1, "function arity mismatch")
    children = [term_metrics(child, bound) for child in term[1:]]
    return 1 + sum(n for n, _ in children), 1 + max((d for _, d in children), default=-1)


def formula_metrics(formula, bound=frozenset()):
    require(isinstance(formula, list) and formula and isinstance(formula[0], str),
            "malformed formula node")
    op = formula[0]
    if op == "=":
        require(len(formula) == 3, "equality arity mismatch")
        children = [term_metrics(child, bound) for child in formula[1:]]
        term_nodes = sum(n for n, _ in children)
        term_depth = max(d for _, d in children)
        return {
            "syntax_nodes": 1 + term_nodes, "formula_nodes": 1,
            "term_nodes": term_nodes, "syntax_depth_edges": 1 + term_depth,
            "formula_depth_edges": 0, "max_term_depth_edges": term_depth,
            "quantifier_nodes": 0, "quantifier_depth": 0,
        }
    is_quantifier = op in ("forall", "exists")
    if is_quantifier:
        require(len(formula) == 3 and isinstance(formula[1], str),
                "malformed quantifier")
        require(formula[1] not in bound, "unnecessary shadowed bound variable")
        children = [formula_metrics(formula[2], bound | {formula[1]})]
    elif op == "not":
        require(len(formula) == 2, "negation arity mismatch")
        children = [formula_metrics(formula[1], bound)]
    elif op == "and":
        require(len(formula) == 3, "conjunction arity mismatch")
        children = [formula_metrics(child, bound) for child in formula[1:]]
    else:
        raise CheckError("formula uses an undeclared logical symbol: " + op)
    return {
        "syntax_nodes": 1 + sum(child["syntax_nodes"] for child in children),
        "formula_nodes": 1 + sum(child["formula_nodes"] for child in children),
        "term_nodes": sum(child["term_nodes"] for child in children),
        "syntax_depth_edges": 1 + max(child["syntax_depth_edges"] for child in children),
        "formula_depth_edges": 1 + max(child["formula_depth_edges"] for child in children),
        "max_term_depth_edges": max(child["max_term_depth_edges"] for child in children),
        "quantifier_nodes": int(is_quantifier) + sum(child["quantifier_nodes"] for child in children),
        "quantifier_depth": int(is_quantifier) + max(child["quantifier_depth"] for child in children),
    }


def verify_theta(theta, dag):
    require(theta[:2] == ["forall", "z"] and len(theta) == 3,
            "theta does not start with forall z")
    existential = theta[2]
    require(existential[:2] == ["exists", "u"] and len(existential) == 3,
            "theta does not continue with exists u")
    gates = dag["gates"]
    r, s = projection_depth(dag["input_count"]), projection_depth(len(gates))
    leaves, leaf_depths = [], []

    def visit(node, expected_leaves, depth):
        if expected_leaves == 1:
            require(node[0] != "and", "balanced conjunction has excess leaf structure")
            leaves.append(node)
            leaf_depths.append(depth)
            return
        require(isinstance(node, list) and len(node) == 3 and node[0] == "and",
                "balanced conjunction is missing an internal conjunction")
        left_count = expected_leaves // 2
        visit(node[1], left_count, depth + 1)
        visit(node[2], expected_leaves - left_count, depth + 1)

    visit(existential[2], len(gates) + 1, 0)
    for index, gate in enumerate(gates):
        op = gate["op"]
        left = projection("u", index, s)
        if op == "input":
            right = projection("z", gate["index"], r)
        elif op in ("0", "1"):
            right = [op]
        else:
            right = [op] + [projection("u", argument, s) for argument in gate["args"]]
        require(leaves[index] == ["=", left, right],
                "theta gate equation differs at gate " + str(index))
    require(leaves[-1] == ["not", ["=", projection("u", dag["output_gate"], s), ["0"]]],
            "theta's final clause is not output != 0")
    return {
        "leaf_count": len(leaves),
        "and_nodes": len(leaves) - 1,
        "max_conjunction_depth_edges": max(leaf_depths),
        "min_conjunction_depth_edges": min(leaf_depths),
    }


def verify_theory(theory, dag):
    require(theory["schema"] == "finite-theory.formulas.v1", "bad formula schema")
    require(theory["signature"] == SIGNATURE, "the functional signature is not the fixed eight symbols")
    require(theory["logical_symbols"] == ["=", "not", "and", "forall", "exists"],
            "unexpected logical vocabulary")
    sentences = theory["sentences"]
    require(isinstance(sentences, list) and len(sentences) == 11,
            "the theory must have exactly eleven sentences")
    require([sentence["name"] for sentence in sentences] == SENTENCE_NAMES,
            "sentence names or ordering differ")
    measured = {}
    for sentence in sentences:
        require(set(sentence) == {"name", "formula"}, "sentence has unexpected fields")
        measured[sentence["name"]] = formula_metrics(sentence["formula"])
    for index, expected in enumerate(ring_and_pair_axioms()):
        require(sentences[index]["formula"] == expected,
                "literal axiom differs: " + SENTENCE_NAMES[index])
    conjunction_metrics = verify_theta(sentences[-1]["formula"], dag)
    totals = {"sentence_count": len(sentences)}
    for field in COUNT_METRICS:
        totals[field] = sum(item[field] for item in measured.values())
    for field in DEPTH_METRICS:
        totals[field] = max(item[field] for item in measured.values())
    return measured, totals, conjunction_metrics


def check(folder):
    dag = load_json(folder / "DAG.json")
    theory = load_json(folder / "theory.json")
    source, residuals, target, source_metrics = verify_sources(folder, dag)
    dag_metrics = verify_dag(dag, source, residuals, target)
    sentence_metrics, theory_metrics, conjunction_metrics = verify_theory(theory, dag)
    computed = {
        "schema": "finite-theory.metrics.v1",
        "source": source_metrics,
        "dag": dag_metrics,
        "sentences": sentence_metrics,
        "theory": theory_metrics,
        "theta_conjunction": conjunction_metrics,
        "files": {name: file_record(folder / name) for name in
                  ("DAG.json", "theory.json", "source_equation.json", "source_expanded_polynomial.json")},
    }
    metrics_path = folder / "metrics.json"
    if metrics_path.exists():
        claimed = load_json(metrics_path)
        for key, value in computed.items():
            require(claimed.get(key) == value, "metrics.json differs at field " + key)
        require(set(claimed) == set(computed), "metrics.json has unexpected fields")
    return computed, metrics_path.exists()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--receipt", type=Path,
                        help="also write a compact verification receipt at this path")
    args = parser.parse_args()
    try:
        computed, matched = check(args.directory.resolve())
    except (CheckError, OSError, KeyError, TypeError, ValueError, IndexError, RecursionError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    receipt = {
        "status": "PASS",
        "checker": "independent standard-library structural and exact-coefficient checker",
        "uses_numerical_zero_tests": False,
        "metrics_file_checked": matched,
        "source": computed["source"],
        "dag": computed["dag"],
        "theta_P": computed["sentences"]["theta_P"],
        "theory": computed["theory"],
        "theta_conjunction": computed["theta_conjunction"],
        "files": computed["files"],
    }
    text = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
