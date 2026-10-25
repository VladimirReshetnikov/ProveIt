#!/usr/bin/env python3
"""Exactly evaluate a residual-list quartic on an integer JSON vector.

Example: python3 code/evaluate.py direct/principal236/equation.json values.json
The program makes no search or claim about the existence of a zero.
"""
from pathlib import Path
import argparse
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("equation", type=Path)
    parser.add_argument("values", type=Path)
    args = parser.parse_args()
    equation = json.loads(args.equation.read_text())
    values = json.loads(args.values.read_text())
    if not isinstance(values, list) or len(values) != len(equation["variables"]):
        raise ValueError("Supply one integer per listed coordinate, in order")
    if not all(type(x) is int for x in values):
        raise ValueError("Every coordinate must be an integer")
    residuals = []
    for row in equation["residuals"]:
        result = 0
        for coefficient, monomial in row["terms"]:
            value = coefficient
            for i in monomial:
                value *= values[i]
            result += value
        residuals.append(result)
    value = sum(r * r for r in residuals)
    print(json.dumps({"value": value, "is_zero": value == 0,
                      "residual_values": residuals}, indent=2))


if __name__ == "__main__":
    main()
