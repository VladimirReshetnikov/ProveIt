#!/usr/bin/env python3
"""Evaluate an emitted sum-of-squares equation at a JSON integer tuple."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tuple", type=Path, help="JSON array of integers")
    parser.add_argument("--profile", choices=("integer248", "integer246", "integer245"),
                        default="integer248")
    parser.add_argument("--residuals", action="store_true")
    args = parser.parse_args()
    equation = json.loads((ROOT / "equations" / args.profile / "equation.json").read_text())
    point = json.loads(args.tuple.read_text())
    if not isinstance(point, list) or len(point) != len(equation["variables"]):
        parser.error(f"the tuple must have {len(equation['variables'])} coordinates")
    if any(type(x) is not int for x in point):
        parser.error("every coordinate must be a JSON integer")
    residuals = []
    for row in equation["residuals"]:
        value = 0
        for coefficient, monomial in row["terms"]:
            term = coefficient
            for index in monomial:
                term *= point[index]
            value += term
        residuals.append(value)
    value = sum(r * r for r in residuals)
    output = {"profile": args.profile, "value": value, "is_zero": value == 0}
    if args.residuals:
        output["residuals"] = residuals
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
