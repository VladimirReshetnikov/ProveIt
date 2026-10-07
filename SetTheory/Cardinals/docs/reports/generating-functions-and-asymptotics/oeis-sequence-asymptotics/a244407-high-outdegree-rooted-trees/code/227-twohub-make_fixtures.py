#!/usr/bin/env python3
"""Explicitly generate exact coefficient fixtures; never fetch or infer OEIS data."""
import argparse
import json
from pathlib import Path
from exact import basic_series, defect_series, cap


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="NEW output file; existing files and symlinks are rejected")
    parser.add_argument("--final-index", type=int, default=64)
    args = parser.parse_args()
    cap(args.final_index, 1, 96, "fixture final index")
    series = basic_series(args.final_index)
    defect = defect_series(series)
    coefficients = {key: series[key] for key in ("r", "H", "G", "F", "J2")}
    coefficients["B"] = defect["B"]
    result = {
        "kind": "exact-generated",
        "final_index": args.final_index,
        "indexing": "r includes indices 0..final_index+2; all other arrays 0..final_index",
        "provenance": "Generated locally by code/make_fixtures.py from integer rooted-tree and Euler-product recurrences; no external sequence terms are inputs.",
        "independent_checks": "code/reproduce.py compares bounded multiset enumeration, direct Euler factors, and canonical colored-tree orbits in their documented finite ranges.",
        "coefficients": coefficients,
    }
    with args.output.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
