#!/usr/bin/env python3
"""Export or check every coefficient of the principal center and norm defect."""
import argparse
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import check

ROOT = Path(__file__).resolve().parent


def expected():
    eq = json.loads((ROOT / "equation.json").read_text())
    algebra = check.actual_center(eq)
    return {
        "variables": check.p.names,
        "weights": check.p.weights,
        "representation": "Each term is [integer coefficient, exponent vector].",
        "center": check.p.serial(algebra["W"]),
        "norm_defect": check.p.serial(algebra["D"]),
        "norm_defect_weighted_degree": 106,
        "norm_defect_leading_terms": check.p.serial(algebra["top"]),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = ROOT / "exact_polynomials.json"
    data = expected()
    if args.check:
        if json.loads(target.read_text()) != data:
            raise SystemExit("Exact polynomial coefficient file differs")
        print("PASS: all 84 center and 594 norm-defect coefficients")
    else:
        target.write_text(json.dumps(data, indent=2) + "\n")
        print("Wrote " + str(target))


if __name__ == "__main__":
    main()
