#!/usr/bin/env python3
"""Export the principal complete quartic in plain mathematical text."""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FOLDER = ROOT / "quartic/fused68/support8"


def monomial(indices):
    powers = Counter(indices)
    return "*".join("x" + str(i) + ("^" + str(p) if p != 1 else "")
                    for i, p in sorted(powers.items()))


def term(coefficient, indices):
    product = monomial(indices)
    magnitude = abs(coefficient)
    return (str(magnitude) if not product else
            product if magnitude == 1 else str(magnitude) + "*" + product)


def polynomial(terms):
    result = ""
    for coefficient, indices in terms:
        if coefficient == 0:
            continue
        sign = (" - " if coefficient < 0 else " + ") if result else ("-" if coefficient < 0 else "")
        result += sign + term(coefficient, indices)
    return result or "0"


def outputs():
    equation = json.loads((FOLDER / "equation.json").read_text())
    expanded = json.loads((FOLDER / "polynomial.json").read_text())
    count = len(equation["variables"])
    rows = equation["residuals"]
    if (count, len(rows), len(expanded["terms"])) != (589, 371, 8156):
        raise ValueError("unexpected principal quartic")
    header = (
        "Complete principal Diophantine equation over unrestricted integers\n"
        "All indices are zero-based. Every xi ranges independently over Z.\n"
        "Q589(x0,...,x588) = sum(fj^2 for j=0,...,370) = 0.\n"
        "The following are all 371 residuals, without omitted terms.\n\n"
    )
    residuals = header + "\n".join(
        "f" + str(j) + " = " + polynomial(row["terms"]) for j, row in enumerate(rows)
    ) + "\n\nVariable index / original retained name / source kind:\n"
    residuals += "\n".join(
        "x" + str(i) + " / " + v["name"] + " / " + v["kind"]
        for i, v in enumerate(equation["variables"])
    ) + "\n"
    full = (
        "Q589(x0,...,x588) = 0, with all xi in Z.\n"
        "Complete expanded polynomial: exact degree 4, 8156 nonzero monomials.\n"
        "The following 8156 signed terms are to be added. Powers use ^.\n\n"
    )
    full += "\n".join(
        ("- " if c < 0 else "+ ") + term(c, indices) for c, indices in expanded["terms"]
    ) + "\n"
    return {"residuals.txt": residuals, "polynomial.txt": full}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, data in outputs().items():
        path = FOLDER / name
        if args.check:
            if path.read_text() != data:
                raise ValueError("plain-text transcription mismatch: " + name)
        else:
            path.write_text(data)
    print("PASS: all 371 residuals and all 8156 monomials in plain text")


if __name__ == "__main__":
    main()

