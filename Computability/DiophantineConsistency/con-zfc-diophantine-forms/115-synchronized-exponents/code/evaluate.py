"""Evaluate either delivered quartic, or the 1074-integer companion.

The input is a JSON array of integers in zero-based coordinate order.
For the integer companion, its order is (a0,b0,c0,a1,b1,c1,...).
This utility performs exact finite arithmetic; it does not search for zeros.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def evaluate_residuals(equation, values):
    if len(values) != len(equation["variables"]):
        raise ValueError("Incorrect number of coordinates")
    if any(type(x) is not int or x < 0 for x in values):
        raise ValueError("Quartic coordinates must be nonnegative integers")
    residuals = []
    for row in equation["residuals"]:
        value = 0
        for coefficient, monomial in row["terms"]:
            product = coefficient
            for index in monomial:
                product *= values[index]
            value += product
        residuals.append(value)
    return sum(value * value for value in residuals)


def evaluate(values, variant="natural358"):
    if variant == "integer1074":
        if len(values) != 1074 or any(type(x) is not int for x in values):
            raise ValueError("The integer companion needs exactly 1074 integer coordinates")
        values = [
            values[i] ** 2 + values[i + 1] ** 2 + values[i + 2] * (values[i + 2] + 1)
            for i in range(0, 1074, 3)
        ]
        variant = "natural358"
    if variant not in ("natural358", "natural361"):
        raise ValueError("Unknown equation variant")
    equation = json.loads((ROOT / "direct" / variant / "equation.json").read_text())
    return evaluate_residuals(equation, values)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coordinates", type=Path, help="JSON file containing the coordinate array")
    parser.add_argument("--variant", choices=["natural358", "natural361", "integer1074"],
                        default="natural358")
    args = parser.parse_args()
    print(evaluate(json.loads(args.coordinates.read_text()), args.variant))
