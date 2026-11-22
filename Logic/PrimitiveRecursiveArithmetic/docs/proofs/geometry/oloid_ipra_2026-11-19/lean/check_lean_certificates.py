#!/usr/bin/env python3
"""Expand the integer identities and proof coefficients in both Lean source files.

This is a small arithmetic cross-check, not a Lean parser or type checker.
It reads only the polynomial-expression fragment used in this packet.
Requires Python 3 and SymPy.
"""
import ast
import operator
import re
from pathlib import Path

import sympy as sp

DIRECTORY = Path(__file__).resolve().parent
BINARY = {ast.Add: operator.add, ast.Sub: operator.sub,
          ast.Mult: operator.mul, ast.Pow: operator.pow}


def polynomial(source, names):
    """Interpret integer literals, named polynomials and ring operations."""
    source = " ".join(source.strip().split()).replace("^", "**")

    def read(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name):
            return names[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -read(node.operand)
        if isinstance(node, ast.BinOp) and type(node.op) in BINARY:
            return BINARY[type(node.op)](read(node.left), read(node.right))
        raise ValueError(ast.dump(node))

    return read(ast.parse(source, mode="eval").body)


def definition(source, name):
    match = re.search(rf"^def {name}\b[^\n]*? :=\s*(.*?)(?=\n(?:\n|def |theorem |/|end ))",
                      source, flags=re.MULTILINE | re.DOTALL)
    if not match:
        raise ValueError(f"missing definition {name}")
    return match[1]


def theorems(source):
    for match in re.finditer(r"^theorem (\w+).*?\(imp (?:circleEqs|\[\]) \("
                             r"(.*?),\s*(.*?)\)\) :=\n(.*?)(?=\n\n)",
                             source, re.MULTILINE | re.DOTALL):
        yield match.groups()


def confirm(name, difference):
    if sp.expand(difference) != 0:
        raise ValueError(f"nonzero residual in {name}")
    print(name, "verified")


def chart():
    source = (DIRECTORY / "ChartAlgebra.lean").read_text()
    variables = "d c a b s".split()
    names = {x: sp.Symbol(x) for x in variables}
    for key in ("Q", "T", "M"):
        names[key] = polynomial(definition(source, key), names)
    vec = {}
    for key in ("N", "W", "E"):
        entries = definition(source, key).strip().removeprefix("⟨").removesuffix("⟩")
        vec[key] = sp.Matrix([polynomial(x, names) for x in entries.split(",")])
    h = definition(source, "circleEqs")
    for idx, (left, right) in enumerate(re.findall(r"\(([^,]+), ([^)]+)\)", h)):
        names[f"H{idx+1}"] = polynomial(left, names) - polynomial(right, names)
    replacements = {}
    for i, axis in enumerate("xyz"):
        names["N"+axis] = vec["N"][i]
        names["cross"+axis] = vec["W"].cross(vec["E"])[i]
        replacements["N."+axis] = "N"+axis
        replacements["(cross W E)."+axis] = "cross"+axis
    for pair in ("NN", "NW", "WW"):
        u, v = pair
        replacements["dot "+u+" "+v] = "dot"+pair
        names["dot"+pair] = vec[u].dot(vec[v])
    count = 0
    for name, left, right, proof in theorems(source):
        for old, new in replacements.items():
            left, right = left.replace(old, new), right.replace(old, new)
        certificate = 0
        if "linear_combination" in proof:
            expr = proof.split("linear_combination")[1].strip()
            # The last parenthesis closes "derive_imp _ _ (by ...)".
            expr = expr.removesuffix(")").replace("h₁", "H1").replace("h₂", "H2")
            expr = re.sub(r"ρ ([0-4])", lambda m: variables[int(m[1])], expr)
            certificate = polynomial(expr, names)
        confirm(name, polynomial(left, names)-polynomial(right, names)-certificate)
        count += 1
    assert count == 9


def periods():
    source = (DIRECTORY / "EllipticReduction.lean").read_text()
    names = {x: sp.Symbol(x) for x in ["x", "d"]}
    operator_text = definition(source, "differential").replace("xP'", "Dpoly")
    count = 0
    for name, left, right, _ in theorems(source):
        row = name.split("_")[0]
        for letter in "FPD":
            key = row+letter
            names[key] = polynomial(definition(source, key), names)
        call = re.search(r"differential (\d+) (\w+) (\w+)", left)
        env = dict(names, j=int(call[1]), P=names[call[2]], Dpoly=names[call[3]])
        names["operatorValue"] = polynomial(operator_text, env)
        confirm(name, polynomial(left.replace(call[0], "operatorValue"), names)
                - polynomial(right, names))
        count += 1
    assert count == 3


if __name__ == "__main__":
    chart()
    periods()
