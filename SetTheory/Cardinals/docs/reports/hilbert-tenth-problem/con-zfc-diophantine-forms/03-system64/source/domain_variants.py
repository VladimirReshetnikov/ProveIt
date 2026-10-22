#!/usr/bin/env python3
"""Generate unrestricted-integer and quadratic variants using only saved JSON.

No giant compiler coefficient is expanded. Coefficient symbols are bound to
the finite, explicit recipe in artifacts/coefficient_recipe.json. All equation
expressions use integer constants, variable/constant identifiers, and binary
addition, subtraction, and multiplication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    def unique(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, "duplicate JSON key: " + key)
            out[key] = value
        return out
    return json.loads(path.read_text(), object_pairs_hook=unique)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pos(a, b, c):
    return ["+", ["+", ["+", 1, ["*", a, a]], ["*", b, b]],
            ["*", c, ["+", c, 1]]]


def identifiers(expr):
    if type(expr) is int:
        return set()
    if isinstance(expr, str):
        return {expr}
    require(isinstance(expr, list) and len(expr) == 3 and
            expr[0] in ("+", "-", "*"), "invalid polynomial AST")
    return identifiers(expr[1]) | identifiers(expr[2])


def degree(expr, environment):
    if type(expr) is int:
        return 0
    if isinstance(expr, str):
        require(expr in environment, "undefined degree identifier: " + expr)
        return environment[expr]
    identifiers(expr)  # Validate the AST, including its opcode.
    a, b = degree(expr[1], environment), degree(expr[2], environment)
    return a + b if expr[0] == "*" else max(a, b)


def balanced_sum(expressions):
    require(bool(expressions), "empty sum")
    values = expressions[:]
    while len(values) > 1:
        values = [["+", values[i], values[i + 1]] if i + 1 < len(values)
                  else values[i] for i in range(0, len(values), 2)]
    return values[0]


def sum_squares(expressions):
    return balanced_sum([["*", expression, expression] for expression in expressions])


def coefficient_bindings(ports, recipe):
    require(len(set(ports)) == len(ports), "duplicate fixed coefficient")
    bindings = {}
    for port in ports:
        if port == "marker_constant":
            meaning = {
                "expression": "2^(inner_bits+2*cell_bits)",
                "fixed_exponent": recipe["inner_bits"] + 2 * recipe["cell_bits"],
            }
        else:
            require(port in recipe["ports"], "missing coefficient recipe: " + port)
            meaning = {"expression": recipe["ports"][port]}
        bindings["coef__" + port] = meaning
    return bindings


def substitute(packet, prefix, expected_variables):
    """Definitions, not quantified registers: only z variables are unknowns."""
    witnesses, fixed = packet["witnesses"], packet["fixed_numerals"]
    require(len(set(witnesses + fixed)) == len(witnesses + fixed), "duplicate port")
    require(set(packet["free"]) == set(witnesses + fixed), "free-port mismatch")
    variables, definitions, images = [], [], {}
    for witness in witnesses:
        triple = [prefix + "__" + witness + "__" + suffix for suffix in ("a", "b", "c")]
        variables.extend(triple)
        name = prefix + "__pos__" + witness
        images[witness] = name
        definitions.append({"name": name, "expression": pos(*triple),
                            "original_positive_witness": witness})
    require(len(variables) == expected_variables, "substitution variable count")
    images.update({name: "coef__" + name for name in fixed})
    known = set(variables) | {"coef__" + name for name in fixed}
    for entry in definitions:
        require(identifiers(entry["expression"]) <= known, "substitution dependency")
        known.add(entry["name"])
    for name, operation, left, right in packet["source"]:
        def rename(operand):
            if type(operand) is int:
                return operand
            require(operand in images, "unscheduled operand: " + str(operand))
            return images[operand]
        new_name = prefix + "__reg__" + name
        expression = [operation, rename(left), rename(right)]
        require(new_name not in known, "register collision")
        require(identifiers(expression) <= known, "undefined source identifier")
        definitions.append({"name": new_name, "expression": expression})
        known.add(new_name)
        images[name] = new_name
    return variables, definitions, images, known


def integer48(packet):
    variables, definitions, images, known = substitute(packet, "z48", 48)
    residuals = []
    for left, right in packet["comparisons"]:
        left = images[left] if isinstance(left, str) else left
        right = images[right] if isinstance(right, str) else right
        residuals.append(["-", left, right])
    require(len(residuals) == 7, "integer48 equation count")
    for residual in residuals:
        require(identifiers(residual) <= known, "undefined output identifier")
    return {
        "domain": "All 48 listed unknowns range independently over Z.",
        "unknowns": variables,
        "definitions_are_not_additional_unknowns": True,
        "definitions": definitions,
        "equations_equal_zero": residuals,
        "equation_total_degrees": [44, 36, 14, 4, 56, 44, 2],
        "max_equation_total_degree": 56,
        "single_polynomial": sum_squares(residuals),
        "single_polynomial_total_degree": 112,
        "source_key": "fixed_marker76_system",
        "projection": "Each source positive witness is its listed Pos expression.",
    }


def integer45(packet):
    variables, definitions, images, known = substitute(packet, "z45", 45)
    output = images[packet["output"]]
    require(output in known and packet["exact_degree"] == 295, "integer45 source degree")
    return {
        "domain": "All 45 listed unknowns range independently over Z.",
        "unknowns": variables,
        "definitions_are_not_additional_unknowns": True,
        "definitions": definitions,
        "polynomial_equal_zero": output,
        "total_degree": 590,
        "source_key": "fixed_marker82",
        "projection": "Each source positive witness is its listed Pos expression.",
    }


def quadratic_lift(packet):
    require(len(packet["source"]) == 64 and len(packet["witnesses"]) == 16,
            "quadratic lift requires the final 64-gate ordinary system")
    require(len(packet["comparisons"]) == 7, "quadratic source equation count")
    fixed = {"coef__" + name for name in packet["fixed_numerals"]}
    variables, equations, images, pos_variables = [], [], {}, []
    for witness in packet["witnesses"]:
        triple = ["pos__" + witness + "__" + suffix for suffix in ("a", "b", "c")]
        inp = "inp__" + witness
        pos_variables.extend(triple)
        variables.extend(triple + [inp])
        images[witness] = inp
        equations.append({"name": "eq_pos__" + witness,
                          "residual": ["-", inp, pos(*triple)]})
    images.update({name: "coef__" + name for name in packet["fixed_numerals"]})
    for name, operation, left, right in packet["source"]:
        def rename(operand):
            if type(operand) is int:
                return operand
            require(operand in images, "unbound lift operand: " + str(operand))
            return images[operand]
        gate = "gate__" + name
        expression = [operation, rename(left), rename(right)]
        variables.append(gate)
        equations.append({"name": "eq_gate__" + name,
                          "residual": ["-", gate, expression]})
        images[name] = gate
    for number, (left, right) in enumerate(packet["comparisons"], 1):
        left = images[left] if isinstance(left, str) else left
        right = images[right] if isinstance(right, str) else right
        equations.append({"name": "eq_output__" + str(number),
                          "residual": ["-", left, right]})
    require(len(variables) == len(set(variables)) == 128, "128-variable count/collision")
    require(len(equations) == len({e["name"] for e in equations}) == 87, "87-equation count")
    known = set(variables) | fixed
    used = set()
    environment = {name: 1 for name in variables}
    environment.update({name: 0 for name in fixed})
    for equation in equations:
        references = identifiers(equation["residual"])
        require(references <= known, "undefined lift identifier")
        used |= references
        equation["total_degree_upper_bound"] = degree(equation["residual"], environment)
        require(equation["total_degree_upper_bound"] <= 2, "nonquadratic equation")
    require(used == known, "unused variable or coefficient in quadratic lift")
    quartic = sum_squares([e["residual"] for e in equations])
    require(degree(quartic, environment) == 4, "quartic degree upper bound")
    first = pos_variables[0]
    require([e["name"] for e in equations if first in identifiers(e["residual"])]
            == [equations[0]["name"]], "distinguished coordinate is not private")
    return {
        "domain": "Every listed unknown ranges over Z; there are no positivity side conditions.",
        "unknowns": variables,
        "unknown_count": 128,
        "unknown_count_breakdown": {"positive_domain_coordinates": 48,
                                    "source_input_variables": 16, "gate_variables": 64},
        "equations_equal_zero": equations,
        "equation_count": 87,
        "equation_count_breakdown": {"domain_equations": 16, "gate_equations": 64,
                                     "output_equations": 7},
        "maximum_equation_degree": 2,
        "quartic_polynomial_equal_zero": quartic,
        "quartic_exact_degree": 4,
        "quartic_degree_certificate": {
            "monomial": {first: 4}, "coefficient": 1,
            "reason": "The coordinate occurs only in the first domain residual, with quadratic term -a^2."
        },
        "source_key": "fixed_marker76_system",
    }


def generate(root):
    paths = {
        "systems": root / "artifacts/fixed_marker_systems.json",
        "polynomials": root / "artifacts/fixed_marker_variants.json",
        "coefficient_recipe": root / "artifacts/coefficient_recipe.json",
    }
    systems, polynomials, recipe = [read_json(paths[k]) for k in paths]
    ordinary, eliminated = systems["fixed_marker76_system"], polynomials["fixed_marker82"]
    require(ordinary["total"] == 64 and ordinary["max_residual_degree"] == 28,
            "wrong ordinary source version")
    require(eliminated["total"] == 82 and len(eliminated["witnesses"]) == 15,
            "wrong eliminated source version")
    require(ordinary["fixed_numerals"] == eliminated["fixed_numerals"], "coefficient interfaces differ")
    return {
        "format": "Integer-polynomial ASTs using +, -, *, integer literals, and identifiers.",
        "positivity_polynomial": "Pos(a,b,c)=1+a*a+b*b+c*(c+1)",
        "coefficient_recipe": "artifacts/coefficient_recipe.json",
        "coefficient_bindings": coefficient_bindings(ordinary["fixed_numerals"], recipe),
        "input_sha256": {str(path.relative_to(root)): digest(path) for path in paths.values()},
        "integer48": integer48(ordinary),
        "integer45": integer45(eliminated),
        "quadratic128": quadratic_lift(ordinary),
        "proof": "proofs/DOMAIN.md",
        "scope": "Exact algebraic/domain transformations of the supplied source; compiler correctness and the source equivalence are inherited.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--check", action="store_true", help="Check the saved output without modifying it.")
    args = parser.parse_args()
    output = args.root / "artifacts/domain_variants.json"
    result = generate(args.root)
    if args.check:
        require(read_json(output) == result, "saved domain artifact differs from generated data")
    else:
        output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "integer_unknown_counts": [45, 48],
                      "quadratic_unknowns": 128, "quadratic_equations": 87,
                      "quartic_exact_degree": 4, "output_sha256": digest(output)}, sort_keys=True))


if __name__ == "__main__":
    main()
