#!/usr/bin/env python3
"""Independently evaluate a JSON sum-of-squares certificate, using only integers.

This verifier does not import the compiler. It checks a supplied assignment,
not the universal correctness or uniqueness theorem for the compiler.
Usage: python code/verify_certificate.py examples/*.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys


def verify(path: Path) -> dict[str, int | str]:
    with path.open(encoding="utf-8") as stream:
        document = json.load(stream)
    if document.get("domain") != "nonnegative integers":
        raise ValueError("Unexpected witness domain")
    if document.get("combination") != "sum of squared residuals":
        raise ValueError("Unexpected polynomial combination")
    variables = document["variables"]
    if not all(isinstance(name, str) for name in variables):
        raise ValueError("Variable names must be strings")
    if len(set(variables)) != len(variables):
        raise ValueError("Duplicate variable names")
    assignment = document["witness"]
    if set(assignment) != set(variables):
        raise ValueError("The witness must assign exactly the listed variables")
    if any(type(v) is not int or v < 0 for v in assignment.values()):
        raise ValueError("Witness coordinates must be nonnegative integers")
    energy = degree = 0
    for residual in document["residuals"]:
        value = 0
        for term in residual["polynomial"]:
            coefficient, monomial = term["coefficient"], term["monomial"]
            if type(coefficient) is not int:
                raise ValueError("Coefficients must be integers")
            if not isinstance(monomial, list) or any(v not in assignment for v in monomial):
                raise ValueError("Invalid monomial")
            degree = max(degree, len(monomial))
            term_value = coefficient
            for variable in monomial:
                term_value *= assignment[variable]
            value += term_value
        energy += value * value
    if degree > 2:
        raise ValueError("A residual exceeds the advertised quadratic bound")
    return {"file": path.name, "variables": len(variables),
            "residuals": len(document["residuals"]),
            "residual_degree": degree, "sum_of_squares": energy}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="+")
    args = parser.parse_args()
    failed = False
    for path in args.files:
        try:
            result = verify(path)
            print(json.dumps(result))
            failed = failed or result["sum_of_squares"] != 0
        except (OSError, ValueError, TypeError, KeyError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
