#!/usr/bin/env python3
"""Independent checker for the exported first-hit polynomial artifacts.

Reconstructs the squared sum from the JSON equations, checks exact equality
with the separately exported expanded quartic, and verifies the assignment.
This checks the algebraic artifacts, not the universality of a source program.
Python 3.10+, standard library only.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def read_polynomial(terms: list, variable_count: int) -> dict[tuple[int, ...], int]:
    result: dict[tuple[int, ...], int] = {}
    for entry in terms:
        if not isinstance(entry, list) or len(entry) != 2:
            raise ValueError("A polynomial term must be [coefficient, indices].")
        coefficient, indices = entry
        if type(coefficient) is not int or not isinstance(indices, list):
            raise ValueError("Invalid coefficient or monomial.")
        if any(type(i) is not int or not 0 <= i < variable_count for i in indices):
            raise ValueError("Variable index out of range.")
        monomial = tuple(sorted(indices))
        result[monomial] = result.get(monomial, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def evaluate(poly: dict, values: list[int]) -> int:
    result = 0
    for indices, coefficient in poly.items():
        product = coefficient
        for index in indices:
            product *= values[index]
        result += product
    return result


def check(folder: Path) -> dict:
    system = json.loads((folder / "certificate_system.json").read_text())
    expanded = json.loads((folder / "expanded_quartic.json").read_text())
    values = json.loads((folder / "certificate_assignment.json").read_text())
    if not isinstance(values, list) or any(type(v) is not int or v < 0 for v in values):
        raise ValueError("All assigned values must be natural numbers.")
    equations = [read_polynomial(e, len(values)) for e in system["equations"]]
    target = read_polynomial(expanded["terms"], len(values))
    if any(len(m) > 2 for p in equations for m in p):
        raise ValueError("A residual has degree greater than two.")
    if any(len(m) > 4 for m in target):
        raise ValueError("Expanded polynomial has degree greater than four.")
    reconstructed: dict[tuple[int, ...], int] = {}
    for equation in equations:
        for left, a in equation.items():
            for right, b in equation.items():
                monomial = tuple(sorted(left + right))
                reconstructed[monomial] = reconstructed.get(monomial, 0) + a * b
    reconstructed = {m: c for m, c in reconstructed.items() if c}
    if target != reconstructed:
        raise ValueError("Expanded polynomial is not the squared sum of the equations.")
    if any(evaluate(p, values) != 0 for p in equations) or evaluate(target, values) != 0:
        raise ValueError("The assigned tuple does not satisfy the polynomial.")
    metadata = system["metadata"]
    free = metadata["free_input_count"]
    if len(equations) != metadata["equation_count"]:
        raise ValueError("Equation-count metadata mismatch.")
    if len(values) - free != metadata["witness_count"]:
        raise ValueError("Witness-count metadata mismatch.")
    for i in range(free, len(values)):
        changed = values.copy()
        changed[i] += 1
        if not any(evaluate(p, changed) for p in equations):
            raise ValueError("A one-coordinate witness mutation unexpectedly passed.")
    return {"status": "PASS", "free_variables": free,
            "natural_witnesses": len(values) - free,
            "equations": len(equations), "expanded_terms": len(target),
            "degree": max(map(len, target), default=0),
            "exact_symbolic_squared_sum_equality": True,
            "assignment_satisfies_every_equation": True,
            "one_coordinate_mutations_rejected": len(values) - free}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folder", type=Path, nargs="?", default=Path("verification"))
    args = parser.parse_args()
    print(json.dumps(check(args.folder), indent=2))


if __name__ == "__main__":
    main()
