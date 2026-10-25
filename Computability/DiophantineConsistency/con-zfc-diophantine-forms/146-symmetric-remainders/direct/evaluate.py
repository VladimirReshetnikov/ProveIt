#!/usr/bin/env python3
"""Evaluate a supplied integer tuple; this does not decide solvability."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def evaluate(equation, values):
    if not isinstance(values, list) or len(values) != len(equation["variables"]):
        raise ValueError("provide exactly one integer per ordered coordinate")
    if any(not isinstance(v, int) or isinstance(v, bool) for v in values):
        raise ValueError("every coordinate must be an integer")
    residuals = []
    for row in equation["residuals"]:
        value = 0
        for coefficient, monomial in row["terms"]:
            term = coefficient
            for v in monomial:
                term *= values[v]
            value += term
        residuals.append(value)
    return {"value": sum(r*r for r in residuals),
            "zero": all(r == 0 for r in residuals),
            "nonzero_residuals": sum(r != 0 for r in residuals),
            "residual_values": residuals}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("tuple_json", type=Path, help="JSON array of all ordered integer coordinates")
    parser.add_argument("--variant", choices=["symmetric_caps", "dimension259"], default="symmetric_caps")
    parser.add_argument("--residuals", action="store_true")
    args = parser.parse_args()
    equation = json.loads((ROOT / "equations" / args.variant / "equation.json").read_text())
    result = evaluate(equation, json.loads(args.tuple_json.read_text()))
    if not args.residuals:
        result.pop("residual_values")
    print(json.dumps(result, sort_keys=True))
