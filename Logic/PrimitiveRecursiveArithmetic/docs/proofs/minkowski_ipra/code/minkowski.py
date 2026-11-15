#!/usr/bin/env python3
"""Exact reference implementation for the finite Minkowski certificate theorem.

This is executable evidence, not a formal proof. All arithmetic is rational or
integer; every search is bounded by data in the certificate. See the paper for
the iPRA argument and lean/ for the explicitly uncompiled formalization outline.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import islice, product
import json
from math import lcm, prod
from pathlib import Path


class InvalidCertificate(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def rational(value) -> Q:
    require(type(value) in (int, str), "Use integer or rational-string data, never floats")
    try:
        return Q(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise InvalidCertificate("Invalid rational number") from exc


def vec(value, n: int) -> tuple[Q, ...]:
    require(isinstance(value, list) and len(value) == n, "Incorrect vector dimension")
    return tuple(rational(x) for x in value)


def dot(a, b) -> Q:
    return sum((x * y for x, y in zip(a, b)), Q(0))


def matvec(a, x) -> tuple[Q, ...]:
    return tuple(dot(row, x) for row in a)


def determinant(a) -> Q:
    """Bounded rational elimination, with at most n pivot searches."""
    n = len(a)
    work = [list(row) for row in a]
    result = Q(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if work[i][j] != 0), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            work[pivot], work[j] = work[j], work[pivot]
            result = -result
        p = work[j][j]
        result *= p
        for i in range(j + 1, n):
            ratio = work[i][j] / p
            for k in range(j + 1, n):
                work[i][k] -= ratio * work[j][k]
            work[i][j] = Q(0)
    return result


def parse_and_check(data: dict) -> dict:
    require(isinstance(data, dict), "Input must be an object")
    require(data.get("schema") == "minkowski-ipra-boxes-v1", "Incorrect schema")
    n = data.get("dimension")
    require(type(n) is int and n > 0, "Dimension must be a positive integer")
    raw_basis = data.get("basis")
    require(isinstance(raw_basis, list) and len(raw_basis) == n, "Incorrect basis shape")
    basis = tuple(vec(row, n) for row in raw_basis)
    det = determinant(basis)
    require(det != 0, "The lattice basis is singular")

    raw_slabs = data.get("slabs")
    require(isinstance(raw_slabs, list) and len(raw_slabs) > 0, "Missing body inequalities")
    slabs = []
    for slab in raw_slabs:
        require(isinstance(slab, dict), "Incorrect slab record")
        normal, bound = vec(slab.get("normal"), n), rational(slab.get("bound"))
        require(bound >= 0, "Slab bound must be nonnegative")
        slabs.append((normal, bound))

    raw_boxes = data.get("boxes")
    require(isinstance(raw_boxes, list) and len(raw_boxes) > 0, "Missing boxes")
    boxes = []
    for box in raw_boxes:
        require(isinstance(box, dict), "Incorrect box record")
        lower, upper = vec(box.get("lower"), n), vec(box.get("upper"), n)
        require(all(l < u for l, u in zip(lower, upper)), "Box must have positive side lengths")
        boxes.append((lower, upper))

    # Pairwise disjoint interiors: one coordinate must separate each pair.
    for i in range(len(boxes)):
        lo, hi = boxes[i]
        for j in range(i):
            other_lo, other_hi = boxes[j]
            require(any(hi[k] <= other_lo[k] or other_hi[k] <= lo[k]
                        for k in range(n)), "Box interiors overlap")

    # For each physical slab |a*x|<=b, test all q in the box at once,
    # where x=2*B*q. An affine function attains its extrema at endpoints.
    for lo, hi in boxes:
        for normal, bound in slabs:
            coeff = tuple(2 * sum((normal[i] * basis[i][k] for i in range(n)), Q(0))
                          for k in range(n))
            minimum = sum((min(coeff[k] * lo[k], coeff[k] * hi[k])
                           for k in range(n)), Q(0))
            maximum = sum((max(coeff[k] * lo[k], coeff[k] * hi[k])
                           for k in range(n)), Q(0))
            require(-bound <= minimum and maximum <= bound,
                    "A normalized box is not contained in half the body")

    volume = sum((prod((u - l for l, u in zip(lo, hi)), start=Q(1))
                  for lo, hi in boxes), Q(0))
    require(volume > 1, "Normalized inner volume must be strictly greater than 1")
    modulus = lcm(*(x.denominator for lo, hi in boxes for x in (*lo, *hi)))
    grid_boxes = []
    for lo, hi in boxes:
        lower = tuple(int(modulus * x) for x in lo)
        upper = tuple(int(modulus * x) for x in hi)
        grid_boxes.append((lower, upper))
    count = sum(prod(u - l for l, u in zip(lo, hi)) for lo, hi in grid_boxes)
    require(Q(count, modulus ** n) == volume, "Internal refinement identity failed")
    require(count > modulus ** n, "Insufficient number of refined cells")
    return dict(n=n, basis=basis, det=det, slabs=slabs, boxes=boxes,
                volume=volume, m=modulus, grid_boxes=grid_boxes, cell_count=count)


def cells(model: dict):
    for box_index, (lo, hi) in enumerate(model["grid_boxes"]):
        for a in product(*(range(l, u) for l, u in zip(lo, hi))):
            yield box_index, a


def in_body(model: dict, x) -> bool:
    return all(abs(dot(a, x)) <= b for a, b in model["slabs"])


def strings(x):
    return [str(y) for y in x]


def extract(data: dict) -> dict:
    model = parse_and_check(data)
    n, m = model["n"], model["m"]
    h = m ** n
    seen = [None] * h
    powers = [m ** k for k in range(n)]
    for j, (box_j, a) in enumerate(islice(cells(model), h + 1)):
        residues = tuple(t % m for t in a)
        color = sum(r * power for r, power in zip(residues, powers))
        prior = seen[color]
        if prior is not None:
            i, box_i, b = prior
            z = tuple((a[k] - b[k]) // m for k in range(n))
            witness_coordinate = next(k for k in range(n) if z[k] != 0)
            c = tuple(Q(2 * a[k] + 1, 2 * m) for k in range(n))
            d = tuple(Q(2 * b[k] + 1, 2 * m) for k in range(n))
            x = matvec(model["basis"], tuple(2 * t for t in c))
            y = matvec(model["basis"], tuple(2 * t for t in d))
            v = matvec(model["basis"], z)
            result = {
                "schema": "minkowski-ipra-witness-v1",
                "dimension": n,
                "modulus": m,
                "number_of_colors": h,
                "total_cells": model["cell_count"],
                "normalized_inner_volume": str(model["volume"]),
                "lattice_covolume": str(abs(model["det"])),
                "cells_examined": j + 1,
                "earlier_index": i,
                "later_index": j,
                "earlier_box": box_i,
                "later_box": box_j,
                "earlier_cell": list(b),
                "later_cell": list(a),
                "residues": list(residues),
                "integer_coefficients": list(z),
                "nonzero_coordinate": witness_coordinate,
                "earlier_center": strings(d),
                "later_center": strings(c),
                "earlier_body_point": strings(y),
                "later_body_point": strings(x),
                "lattice_point": strings(v),
            }
            verify_witness(data, result)
            return result
        seen[color] = (j, box_j, a)
    raise RuntimeError("Valid certificate contradicted the finite pigeonhole invariant")


def verify_witness(data: dict, witness: dict) -> bool:
    """Independent arithmetic check of the geometric witness, not search replay."""
    model = parse_and_check(data)
    n, m = model["n"], model["m"]
    require(isinstance(witness, dict), "Witness must be an object")
    require(witness.get("schema") == "minkowski-ipra-witness-v1", "Incorrect witness schema")
    for key in ("dimension", "modulus", "number_of_colors", "total_cells",
                "cells_examined", "earlier_index", "later_index", "earlier_box",
                "later_box", "nonzero_coordinate"):
        require(type(witness.get(key)) is int, f"Witness field {key} must be an integer")
    require(witness.get("dimension") == n and witness.get("modulus") == m, "Witness dimensions differ")

    def integer_vector(key):
        x = witness.get(key)
        require(isinstance(x, list) and len(x) == n and all(type(t) is int for t in x),
                "Incorrect integer vector")
        return tuple(x)

    a = integer_vector("later_cell")
    b = integer_vector("earlier_cell")
    z = integer_vector("integer_coefficients")
    require(a != b, "Collision points must be distinct")
    require(any(t != 0 for t in z), "Zero lattice coefficient vector")
    require(all(a[k] - b[k] == m * z[k] for k in range(n)), "Scaled difference is incorrect")
    require(integer_vector("residues") == tuple(t % m for t in a) == tuple(t % m for t in b),
            "Residues do not match")
    for key, point in (("later_box", a), ("earlier_box", b)):
        j = witness.get(key)
        require(type(j) is int and 0 <= j < len(model["grid_boxes"]), "Incorrect box index")
        lo, hi = model["grid_boxes"][j]
        require(all(lo[k] <= point[k] < hi[k] for k in range(n)), "Cell lies outside its box")
        offset = sum(prod(u - l for l, u in zip(other_lo, other_hi))
                     for other_lo, other_hi in model["grid_boxes"][:j])
        local = sum((point[k] - lo[k]) * prod(hi[t] - lo[t] for t in range(k + 1, n))
                    for k in range(n))
        index_key = "later_index" if key == "later_box" else "earlier_index"
        require(witness.get(index_key) == offset + local, "Incorrect enumeration index")
    earlier, later = witness["earlier_index"], witness["later_index"]
    require(0 <= earlier < later <= m ** n, "Collision indices violate the search bound")
    require(witness.get("cells_examined") == later + 1, "Incorrect cell count")
    require(witness.get("number_of_colors") == m ** n, "Incorrect color count")
    require(witness.get("total_cells") == model["cell_count"], "Incorrect total cell count")
    require(rational(witness.get("normalized_inner_volume")) == model["volume"], "Incorrect inner volume")
    require(rational(witness.get("lattice_covolume")) == abs(model["det"]), "Incorrect covolume")
    k = witness.get("nonzero_coordinate")
    require(type(k) is int and 0 <= k < n and z[k] != 0, "Incorrect nonzero coordinate")
    c = tuple(Q(2 * a[k] + 1, 2 * m) for k in range(n))
    d = tuple(Q(2 * b[k] + 1, 2 * m) for k in range(n))
    x = matvec(model["basis"], tuple(2 * t for t in c))
    y = matvec(model["basis"], tuple(2 * t for t in d))
    v = matvec(model["basis"], z)
    require(vec(witness.get("later_center"), n) == c, "Incorrect later center")
    require(vec(witness.get("earlier_center"), n) == d, "Incorrect earlier center")
    require(vec(witness.get("later_body_point"), n) == x, "Incorrect later body point")
    require(vec(witness.get("earlier_body_point"), n) == y, "Incorrect earlier body point")
    require(vec(witness.get("lattice_point"), n) == v, "Incorrect lattice point")
    require(all((x[k] - y[k]) / 2 == v[k] for k in range(n)), "Midpoint identity failed")
    require(in_body(model, x) and in_body(model, y) and in_body(model, v), "Body membership failed")
    require(any(t != 0 for t in v), "Physical lattice point is zero")
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--verify", type=Path, help="Check an existing witness instead of extracting")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    if args.verify:
        verify_witness(data, json.loads(args.verify.read_text()))
        result = {"verified": True}
    else:
        result = extract(data)
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
