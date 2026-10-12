"""Fraction-based producer for exact relative homology quotient certificates.

Solve the block system [[d3,j2],[0,e2]]*(a,b)=(s,0).  Gaussian row
provenance turns an inconsistent row into a dual obstruction certificate.
All outputs are integral after denominator clearing.  Geometry is external.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd, lcm
from pathlib import Path
import sys

try:
    from .verify import CERT_SCHEMA, input_digest, validate_input
except ImportError:
    from verify import CERT_SCHEMA, input_digest, validate_input


def _clear_denominators(values: list[Fraction]) -> list[int]:
    scale = 1
    for value in values:
        scale = lcm(scale, value.denominator)
    integers = [int(value * scale) for value in values]
    common = 0
    for value in integers:
        common = gcd(common, abs(value))
    if common > 1:
        integers = [value // common for value in integers]
    return integers


def produce(data: dict) -> dict:
    """Produce one exact supported or outside certificate for validated data."""
    dims = validate_input(data)
    c2, c3, e1, e2 = (dims[name] for name in ("c2", "c3", "e1", "e2"))
    rows, cols = c2 + e1, c3 + e2
    block = [data["d3"][i] + data["j2"][i] for i in range(c2)]
    block += [[0] * c3 + data["e2"][i] for i in range(e1)]
    rhs = data["s"] + [0] * e1
    augmented = [[Fraction(x) for x in block[i] + [rhs[i]]] for i in range(rows)]
    provenance = [[Fraction(int(i == j)) for j in range(rows)] for i in range(rows)]
    pivots: list[tuple[int, int]] = []
    pivot_row = 0
    for col in range(cols):
        selected = next((i for i in range(pivot_row, rows) if augmented[i][col]), None)
        if selected is None:
            continue
        augmented[pivot_row], augmented[selected] = augmented[selected], augmented[pivot_row]
        provenance[pivot_row], provenance[selected] = provenance[selected], provenance[pivot_row]
        pivot = augmented[pivot_row][col]
        augmented[pivot_row] = [value / pivot for value in augmented[pivot_row]]
        provenance[pivot_row] = [value / pivot for value in provenance[pivot_row]]
        for i in range(rows):
            if i == pivot_row or not augmented[i][col]:
                continue
            multiple = augmented[i][col]
            augmented[i] = [
                value - multiple * pivot_value
                for value, pivot_value in zip(augmented[i], augmented[pivot_row])
            ]
            provenance[i] = [
                value - multiple * pivot_value
                for value, pivot_value in zip(provenance[i], provenance[pivot_row])
            ]
        pivots.append((pivot_row, col))
        pivot_row += 1
        if pivot_row == rows:
            break
    base = {"schema": CERT_SCHEMA, "input_sha256": input_digest(data)}
    for i in range(rows):
        if all(value == 0 for value in augmented[i][:cols]) and augmented[i][cols] != 0:
            contradiction = augmented[i][cols]
            # lambda*A=0 and lambda*rhs=contradiction.  Its lower block is -U.
            y = [value / contradiction for value in provenance[i][:c2]]
            u = [-value / contradiction for value in provenance[i][c2:]]
            integers = _clear_denominators(y + u + [Fraction(1)])
            return {
                **base,
                "kind": "outside",
                "Y": integers[:c2],
                "U": integers[c2:c2 + e1],
                "q": integers[-1],
            }
    solution = [Fraction(0) for _ in range(cols)]
    for row, col in pivots:
        solution[col] = augmented[row][cols]
    integers = _clear_denominators(solution + [Fraction(1)])
    return {
        **base,
        "kind": "supported",
        "a": integers[:c3],
        "b": integers[c3:c3 + e2],
        "q": integers[-1],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("-o", "--output", type=Path)
    args = parser.parse_args(argv)
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        certificate = produce(data)
        encoded = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.write_text(encoded, encoding="utf-8")
        else:
            print(encoded, end="")
    except (OSError, ValueError) as error:
        print(f"certificate production failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
