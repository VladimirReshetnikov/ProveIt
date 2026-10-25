#!/usr/bin/env python3
"""Exactly evaluate the delivered polynomial at an explicit integer tuple."""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def polynomial_value(terms, point):
    total = 0
    for coefficient, monomial in terms:
        value = coefficient
        for index in monomial:
            value *= point[index]
        total += value
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tuple", type=Path, help="JSON list in z_1,...,z_247 order")
    parser.add_argument("--expanded", action="store_true",
                        help="also evaluate the collected polynomial and compare")
    parser.add_argument("--nonzero-rows", action="store_true")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    point = json.loads(args.tuple.read_text())
    require(type(point) is list and len(point) == 247,
            "Expected a JSON list of exactly 247 integers.")
    require(all(type(value) is int for value in point),
            "Every coordinate must be a JSON integer; booleans and decimals are rejected.")
    equation = json.loads((ROOT/"equations/quartic247/equation.json").read_text())
    values = [polynomial_value(row["terms"], point) for row in equation["residuals"]]
    total = sum(value*value for value in values)
    result = {"value": total, "is_zero": total == 0,
              "nonzero_residual_count": sum(value != 0 for value in values)}
    if args.expanded:
        expanded = json.loads((ROOT/"equations/quartic247/expanded_polynomial.json").read_text())
        check = polynomial_value(expanded["terms"], point)
        require(check == total, "Residual and expanded evaluation disagree.")
        result["expanded_evaluation_agrees"] = True
    if args.nonzero_rows:
        result["nonzero_residuals"] = {
            "R_"+str(i+1): value for i, value in enumerate(values) if value != 0
        }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
