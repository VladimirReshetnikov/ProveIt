#!/usr/bin/env python3
"""Rebuild the small exact example inputs and output witnesses."""

from pathlib import Path
import json

from grid_certificate import from_grid
from minkowski import extract, rational, dot, require


def build():
    square = {
        "schema": "minkowski-ipra-boxes-v1", "dimension": 2,
        "basis": [["1", "0"], ["0", "1"]],
        "slabs": [{"normal": ["1", "0"], "bound": "3/2"},
                  {"normal": ["0", "1"], "bound": "3/2"}],
        "boxes": [{"lower": ["-3/4", "-3/4"], "upper": ["3/4", "3/4"]}],
    }
    skew = {
        **square,
        "basis": [["2", "1"], ["0", "1"]],
        "slabs": [{"normal": ["1", "-1"], "bound": "3"},
                  {"normal": ["0", "1"], "bound": "3/2"}],
    }
    diamond_body = {
        "dimension": 2, "basis": [["1", "0"], ["0", "1"]],
        "slabs": [{"normal": ["1", "1"], "bound": "3/2"},
                  {"normal": ["1", "-1"], "bound": "3/2"}],
    }
    diamond = from_grid(diamond_body, 16, "3/2")
    cube3 = {
        "schema": "minkowski-ipra-boxes-v1", "dimension": 3,
        "basis": [["1", "0", "0"], ["0", "1", "0"], ["0", "0", "1"]],
        "slabs": [{"normal": [str(int(i == j)) for j in range(3)], "bound": "3/2"}
                  for i in range(3)],
        "boxes": [{"lower": ["-3/4"] * 3, "upper": ["3/4"] * 3}],
    }
    return {"square": square, "skew_lattice": skew, "diamond": diamond, "cube3": cube3}


def main():
    directory = Path(__file__).resolve().parents[1] / "examples"
    directory.mkdir(exist_ok=True)
    summary = []
    for name, data in build().items():
        witness = extract(data)
        (directory / f"{name}.json").write_text(json.dumps(data, indent=2) + "\n")
        (directory / f"{name}.witness.json").write_text(json.dumps(witness, indent=2) + "\n")
        summary.append({"name": name, "mesh": witness["modulus"],
                        "cells": witness["total_cells"], "colors": witness["number_of_colors"],
                        "examined": witness["cells_examined"],
                        "z": witness["integer_coefficients"], "point": witness["lattice_point"]})
    # Exact-threshold rational square: integer facets have b_max=1, hence
    # lambda=3/2. Its enlargement is the square certificate above. Check
    # that the extracted point also belongs to the original area-4 square.
    w = extract(build()["square"])
    point = [rational(t) for t in w["lattice_point"]]
    require(all(abs(t) <= 1 for t in point), "Equality-case return failed")
    equality = {"original_body": "[-1,1]^2", "original_volume": "4",
                "integer_facet_maximum": 1, "enlargement": "3/2",
                "strict_certificate": "square.json", "lattice_point": w["lattice_point"],
                "verified_original_membership": True}
    (directory / "rational_equality.json").write_text(json.dumps(equality, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
