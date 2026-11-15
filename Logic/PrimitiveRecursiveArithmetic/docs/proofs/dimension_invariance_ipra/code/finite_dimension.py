#!/usr/bin/env python3
"""Exact finite witnesses for constructive invariance of dimension.

This is an executable audit of the finite theorem, not a proof assistant.
All coordinates are rational.  There are no floating-point comparisons.

Input JSON::

    {"d": 2, "m": 1, "N": 1, "delta": "1",
     "table": [["0"], ["1"], ["3"], ["2"]]}

Rows are ordered lexicographically by (0,...,0), ..., (N,...,N), with the
last coordinate varying fastest.  For d > m, N >= 1 and delta > 0 the
algorithm returns one of two finite certificates:

* an opposite-face pair whose image distance is < delta; or
* two vertices of one Kuhn simplex whose image distance is >= delta / d.

The second branch uses staggered half-open cells, Sperner labels, a bounded
search for a fully labelled simplex, and a threshold collision.  It does not
find its answer by searching all simplex pairs for large variation.

Usage: python3 finite_dimension.py input.json [--check certificate.json]
       python3 finite_dimension.py --example

The independent checker validates just the witness needed for the theorem;
the additional extraction trace is explanatory and need not be trusted.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
from typing import Any, Iterator

Point = tuple[int, ...]
Vector = tuple[Fraction, ...]


def rational(value: Any) -> Fraction:
    """Accept exact JSON integers and rational strings, never binary floats."""
    if isinstance(value, bool) or not isinstance(value, (int, str, Fraction)):
        raise ValueError("coordinates must be integers or exact rational strings")
    return Fraction(value)


def qstr(value: Fraction) -> str:
    return str(value)


def sup_distance(left: Vector, right: Vector) -> Fraction:
    return max((abs(a - b) for a, b in zip(left, right)), default=Fraction(0))


def grid_points(d: int, N: int) -> Iterator[Point]:
    return product(range(N + 1), repeat=d)


def simplex_vertices(base: Point, permutation: tuple[int, ...]) -> tuple[Point, ...]:
    current = list(base)
    vertices = [tuple(current)]
    for axis in permutation:
        current = current.copy()
        current[axis] += 1
        vertices.append(tuple(current))
    return tuple(vertices)


def kuhn_simplices(d: int, N: int):
    """Enumerate the N^d d! maximal simplices; dimension zero has one."""
    for base in product(range(N), repeat=d):
        for permutation in permutations(range(d)):
            yield base, permutation, simplex_vertices(base, permutation)


@dataclass(frozen=True)
class Instance:
    d: int
    m: int
    N: int
    delta: Fraction
    table: dict[Point, Vector]

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "Instance":
        d, m, N = data["d"], data["m"], data["N"]
        if any(isinstance(x, bool) or not isinstance(x, int) for x in (d, m, N)):
            raise ValueError("d, m and N must be integers")
        if d < 0 or m < 0 or N < 1:
            raise ValueError("require d,m >= 0 and N >= 1")
        delta = rational(data["delta"])
        if delta <= 0:
            raise ValueError("delta must be positive")
        rows = data["table"]
        if len(rows) != (N + 1) ** d:
            raise ValueError("table must have exactly (N+1)^d rows")
        if any(len(row) != m for row in rows):
            raise ValueError("every table row must have exactly m entries")
        table = {v: tuple(rational(x) for x in row)
                 for v, row in zip(grid_points(d, N), rows)}
        return cls(d, m, N, delta, table)

    def to_json(self) -> dict[str, Any]:
        return {"d": self.d, "m": self.m, "N": self.N,
                "delta": qstr(self.delta),
                "table": [[qstr(x) for x in self.table[v]]
                          for v in grid_points(self.d, self.N)]}


def cell_of(value: Vector, axis: int, d: int, delta: Fraction) -> tuple[int, ...]:
    """Target partition shifted by axis*delta/d, with axis in 0,...,d-1."""
    offset = Fraction(axis, d)
    shifted = (y / delta - offset for y in value)
    return tuple(y.numerator // y.denominator for y in shifted)


def staggered_data(instance: Instance):
    d, N, table, delta = instance.d, instance.N, instance.table, instance.delta
    cells = {(i, v): cell_of(table[v], i, d, delta)
             for i in range(d) for v in table}
    occupied = [{cells[i, v] for v in table if v[i] == 0} for i in range(d)]
    bits = {v: tuple(int(cells[i, v] not in occupied[i]) for i in range(d))
            for v in table}
    # Colours 0,...,d: first zero bit, or d if all bits equal one.
    labels = {v: next((i for i in range(d) if bits[v][i] == 0), d)
              for v in table}
    return cells, bits, labels


def extract(instance: Instance) -> dict[str, Any]:
    d, m, N, delta, table = (instance.d, instance.m, instance.N,
                             instance.delta, instance.table)
    if d <= m:
        raise ValueError("the obstruction certificate requires d > m")

    # The first alternative is checked on a manifestly bounded pair list.
    for i in range(d):
        lower = [v for v in table if v[i] == 0]
        upper = [v for v in table if v[i] == N]
        for u in lower:
            for v in upper:
                distance = sup_distance(table[u], table[v])
                if distance < delta:
                    return {"kind": "opposite_face_failure", "source_axis": i,
                            "u": list(u), "v": list(v),
                            "distance": qstr(distance), "bound": qstr(delta)}

    # If m=0, the first alternative necessarily occurred, since delta>0.
    if m == 0:
        raise AssertionError("empty target has distance zero on every pair")

    cells, bits, labels = staggered_data(instance)
    for base, permutation, vertices in kuhn_simplices(d, N):
        if {labels[v] for v in vertices} == set(range(d + 1)):
            break
    else:
        raise AssertionError("finite cubical Sperner theorem violated")

    by_colour = {labels[v]: v for v in vertices}
    common = by_colour[d]  # All d bits are one at this vertex.
    thresholds = []
    for i in range(d):
        zero = by_colour[i]
        assert bits[zero][i] == 0 and bits[common][i] == 1
        c0, c1 = cells[i, zero], cells[i, common]
        j = next(j for j in range(m) if c0[j] != c1[j])
        lattice_index = min(c0[j], c1[j]) + 1
        threshold = delta * (lattice_index + Fraction(i, d))
        lo, hi = sorted((table[zero][j], table[common][j]))
        assert lo < threshold <= hi
        thresholds.append({"source_axis": i, "target_axis": j,
                           "lattice_index": lattice_index,
                           "threshold": qstr(threshold),
                           "zero_vertex": list(zero),
                           "one_vertex": list(common)})

    first_on_axis: dict[int, int] = {}
    for i, threshold in enumerate(thresholds):
        j = threshold["target_axis"]
        if j in first_on_axis:
            earlier = first_on_axis[j]
            break
        first_on_axis[j] = i
    else:
        raise AssertionError("bounded pigeonhole principle violated")

    a = rational(thresholds[earlier]["threshold"])
    b = rational(thresholds[i]["threshold"])
    assert abs(a - b) >= delta / d
    u = min(vertices, key=lambda v: table[v][j])
    v = max(vertices, key=lambda v: table[v][j])
    coordinate_gap = table[v][j] - table[u][j]
    assert coordinate_gap >= abs(a - b) >= delta / d
    return {
        "kind": "simplex_variation",
        "base": list(base), "permutation": list(permutation),
        "vertices": [list(v) for v in vertices],
        "labels": [labels[v] for v in vertices],
        "u": list(u), "v": list(v), "target_axis": j,
        "distance": qstr(sup_distance(table[u], table[v])),
        "coordinate_gap": qstr(coordinate_gap), "bound": qstr(delta / d),
        "thresholds": thresholds, "collision": [earlier, i],
    }


def verify_certificate(instance: Instance, certificate: dict[str, Any]) -> bool:
    """Check the finite conclusion independently of the extraction trace."""
    try:
        if instance.d <= instance.m:
            return False
        u, v = tuple(certificate["u"]), tuple(certificate["v"])
        if any(type(a) is not int for a in u + v):
            return False
        if u not in instance.table or v not in instance.table:
            return False
        gap = sup_distance(instance.table[u], instance.table[v])
        if certificate["kind"] == "opposite_face_failure":
            i = certificate["source_axis"]
            return (type(i) is int and 0 <= i < instance.d
                    and u[i] == 0 and v[i] == instance.N and gap < instance.delta)
        if certificate["kind"] == "simplex_variation":
            base, permutation = (tuple(certificate["base"]),
                                 tuple(certificate["permutation"]))
            if (len(base) != instance.d
                    or any(type(a) is not int or not 0 <= a < instance.N
                           for a in base)
                    or any(type(i) is not int for i in permutation)
                    or sorted(permutation) != list(range(instance.d))):
                return False
            vertices = simplex_vertices(base, permutation)
            return u in vertices and v in vertices and gap >= instance.delta / instance.d
        return False
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError):
        return False


EXAMPLE = {"d": 2, "m": 1, "N": 1, "delta": "1",
           "table": [["0"], ["1"], ["3"], ["2"]]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--example", action="store_true")
    args = parser.parse_args()
    if args.example:
        data = EXAMPLE
    elif args.input:
        data = json.loads(args.input.read_text())
    else:
        parser.error("provide input.json or --example")
    instance = Instance.from_json(data)
    if args.check:
        certificate = json.loads(args.check.read_text())
        valid = verify_certificate(instance, certificate)
        print(json.dumps({"valid": valid}, indent=2))
        raise SystemExit(0 if valid else 1)
    certificate = extract(instance)
    assert verify_certificate(instance, certificate)
    print(json.dumps(certificate, indent=2))


if __name__ == "__main__":
    main()
