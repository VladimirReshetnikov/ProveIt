#!/usr/bin/env python3
"""Exhaustive symbolic audit of the cuboid face-chain unfoldings.

The audit has two parts.

1. Fixed vertex to the top face.  It enumerates every simple chain in the
   six-face adjacency graph, starting in a face incident with the origin and
   ending in the top face.  Unfolding gives 28 distinct source images.  Four
   canonical images suffice: every other image is farther than one canonical
   image throughout the top rectangle.  Since a squared-distance difference
   is affine in the target point, four corner checks certify each domination.

2. Antipodal base-to-top pair.  It enumerates every simple chain from the
   bottom to the top.  There are 14 distinct squared net lengths.  Five are the
   d1,...,d5 formulas in the paper; each of the nine others exceeds one of
   those five by an explicitly nonnegative factorization.

This is an executable finite certificate for the unfolding classification. It
is not a substitute for a formal Lean proof of the general straightening and
unfolding lemmas.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import sympy as sp

A, B, C = sp.symbols("A B C", positive=True, real=True)
p, q, x, y = sp.symbols("p q x y", real=True)
U, V = sp.symbols("U V", nonnegative=True, real=True)
X, Y = sp.symbols("X Y", nonnegative=True, real=True)
SIDES = (A, B, C)

Vertex = tuple[int, int, int]
Point2 = tuple[sp.Expr, sp.Expr]

VERTICES: tuple[Vertex, ...] = tuple(
    (i, j, k) for i in (0, 1) for j in (0, 1) for k in (0, 1)
)
FACES: dict[str, tuple[Vertex, ...]] = {
    "x0": tuple(v for v in VERTICES if v[0] == 0),
    "x1": tuple(v for v in VERTICES if v[0] == 1),
    "y0": tuple(v for v in VERTICES if v[1] == 0),
    "y1": tuple(v for v in VERTICES if v[1] == 1),
    "z0": tuple(v for v in VERTICES if v[2] == 0),
    "z1": tuple(v for v in VERTICES if v[2] == 1),
}
AXIS = {"x0": 0, "x1": 0, "y0": 1, "y1": 1, "z0": 2, "z1": 2}
ADJACENT: dict[str, tuple[str, ...]] = {
    f: tuple(g for g in FACES if AXIS[f] != AXIS[g]) for f in FACES
}


def vadd(a: Point2, b: Point2) -> Point2:
    return (sp.expand(a[0] + b[0]), sp.expand(a[1] + b[1]))


def vsub(a: Point2, b: Point2) -> Point2:
    return (sp.expand(a[0] - b[0]), sp.expand(a[1] - b[1]))


def vscale(t: sp.Expr, a: Point2) -> Point2:
    return (sp.expand(t * a[0]), sp.expand(t * a[1]))


def vmean(points: Iterable[Point2]) -> Point2:
    values = tuple(points)
    sx = sum((z[0] for z in values), sp.Integer(0)) / len(values)
    sy = sum((z[1] for z in values), sp.Integer(0)) / len(values)
    return (sp.expand(sx), sp.expand(sy))


TOP_PLACEMENT: dict[Vertex, Point2] = {
    v: (sp.expand(A * v[0]), sp.expand(B * v[1])) for v in FACES["z1"]
}


def place_previous_face(
    current: str, previous: str, current_positions: dict[Vertex, Point2]
) -> dict[Vertex, Point2]:
    """Reflect the previous rectangle across the common edge in the net."""

    shared = tuple(sorted(set(FACES[current]) & set(FACES[previous])))
    if len(shared) != 2:
        raise AssertionError((current, previous, shared))
    current_other = tuple(v for v in FACES[current] if v not in shared)

    edge_mid = vmean(current_positions[v] for v in shared)
    interior_mid = vmean(current_positions[v] for v in current_other)
    interior = vsub(interior_mid, edge_mid)

    # The perpendicular width inside the current face is exactly the side
    # length along the axis fixed by the previous face.  Dividing therefore
    # yields one of the four coordinate unit normals in the planar net.
    current_width = SIDES[AXIS[previous]]
    normal = (
        sp.simplify(interior[0] / current_width),
        sp.simplify(interior[1] / current_width),
    )
    if any(component not in (sp.Integer(-1), sp.Integer(0), sp.Integer(1)) for component in normal):
        raise AssertionError((current, previous, normal))

    previous_width = SIDES[AXIS[current]]
    result: dict[Vertex, Point2] = {v: current_positions[v] for v in shared}
    for vertex in shared:
        opposite = list(vertex)
        opposite[AXIS[current]] = 1 - opposite[AXIS[current]]
        opposite_vertex = tuple(opposite)
        if opposite_vertex not in FACES[previous]:
            raise AssertionError((current, previous, vertex, opposite_vertex))
        result[opposite_vertex] = vsub(
            current_positions[vertex], vscale(previous_width, normal)
        )
    return result


def simple_paths(starts: Iterable[str], end: str) -> list[tuple[str, ...]]:
    paths: list[tuple[str, ...]] = []

    def visit(path: tuple[str, ...]) -> None:
        face = path[-1]
        if face == end:
            paths.append(path)
            return
        for next_face in ADJACENT[face]:
            if next_face not in path:
                visit(path + (next_face,))

    for start in starts:
        visit((start,))
    return paths


def unfold(path: tuple[str, ...]) -> dict[str, dict[Vertex, Point2]]:
    if path[-1] != "z1":
        raise ValueError("The target face must be z1.")
    placements: dict[str, dict[Vertex, Point2]] = {"z1": TOP_PLACEMENT}
    current = "z1"
    for previous in reversed(path[:-1]):
        placements[previous] = place_previous_face(
            current, previous, placements[current]
        )
        current = previous
    return placements


def squared_distance(z: Point2, w: Point2) -> sp.Expr:
    return sp.expand((z[0] - w[0]) ** 2 + (z[1] - w[1]) ** 2)


def point_on_bottom(placement: dict[Vertex, Point2]) -> Point2:
    origin = placement[(0, 0, 0)]
    along_x = vsub(placement[(1, 0, 0)], origin)
    along_y = vsub(placement[(0, 1, 0)], origin)
    return vadd(origin, vadd(vscale(x / A, along_x), vscale(y / B, along_y)))


def polynomial_has_nonnegative_coefficients(expr: sp.Expr) -> bool:
    poly = sp.Poly(sp.expand(expr), A, U, V)
    return all(coefficient >= 0 for coefficient in poly.coeffs())


@dataclass(frozen=True)
class FixedDomination:
    source: Point2
    canonical_index: int
    corner_certificates: tuple[sp.Expr, sp.Expr, sp.Expr, sp.Expr]


def audit_fixed_vertex() -> tuple[list[tuple[str, ...]], list[Point2], list[FixedDomination]]:
    paths = simple_paths(("x0", "y0", "z0"), "z1")
    images_by_path: list[Point2] = []
    for path in paths:
        placement = unfold(path)
        image = tuple(sp.expand(t) for t in placement[path[0]][(0, 0, 0)])
        images_by_path.append(image)  # type: ignore[arg-type]

    images = sorted(set(images_by_path), key=lambda z: (str(z[0]), str(z[1])))
    canonical: tuple[Point2, ...] = (
        (-C, sp.Integer(0)),
        (A + C, -A),
        (sp.Integer(0), -C),
        (-B, B + C),
    )
    if not all(site in images for site in canonical):
        raise AssertionError("A canonical source image was not enumerated.")

    target = (p, q)
    corners = ((0, 0), (A, 0), (0, B), (A, B))
    substitutions = {B: A + U, C: A + U + V}
    dominations: list[FixedDomination] = []

    for source in images:
        if source in canonical:
            continue
        found: FixedDomination | None = None
        for index, site in enumerate(canonical, start=1):
            difference = sp.expand(
                squared_distance(target, source) - squared_distance(target, site)
            )
            certificates = tuple(
                sp.expand(difference.subs({p: px, q: qy}).subs(substitutions))
                for px, qy in corners
            )
            if all(polynomial_has_nonnegative_coefficients(value) for value in certificates):
                found = FixedDomination(source, index, certificates)  # type: ignore[arg-type]
                break
        if found is None:
            raise AssertionError(("undominated fixed source", source))
        dominations.append(found)

    if len(paths) != 80 or len(images) != 28 or len(dominations) != 24:
        raise AssertionError((len(paths), len(images), len(dominations)))
    return paths, images, dominations


@dataclass(frozen=True)
class DiameterExtra:
    chains: tuple[tuple[str, ...], ...]
    squared_length: sp.Expr
    canonical_name: str
    gap: sp.Expr
    gap_display: str


def audit_diameter() -> tuple[list[tuple[str, ...]], dict[str, sp.Expr], list[DiameterExtra]]:
    paths = simple_paths(("z0",), "z1")
    endpoint_top = (A - x, B - y)
    expressions: defaultdict[sp.Expr, list[tuple[str, ...]]] = defaultdict(list)

    for path in paths:
        placement = unfold(path)
        bottom_image = point_on_bottom(placement["z0"])
        expression = sp.expand(squared_distance(endpoint_top, bottom_image))
        expressions[expression].append(path)

    canonical: dict[str, sp.Expr] = {
        "d1^2": sp.expand((A + C) ** 2 + (B - 2 * y) ** 2),
        "d2^2": sp.expand((B + C) ** 2 + (A - 2 * x) ** 2),
        "d3^2": sp.expand((C + x + y) ** 2 + (A + B - x - y) ** 2),
        "d4^2": sp.expand((A + B) ** 2 + (C + 2 * y) ** 2),
        "d5^2": sp.expand((A + B) ** 2 + (C + 2 * x) ** 2),
    }
    if not all(value in expressions for value in canonical.values()):
        raise AssertionError("A canonical diameter unfolding was not enumerated.")

    # Use X=A-2x and Y=B-2y.  The normalized domain gives
    # 0 <= X <= A and 0 <= Y <= B.
    xy_substitution = {x: (A - X) / 2, y: (B - Y) / 2}
    target_gaps: tuple[tuple[str, sp.Expr, str], ...] = (
        ("d3^2", 2 * (A + B) * (A + B - X - Y),
         "2*(A+B)*(A+B-X-Y)"),
        ("d3^2", 2 * Y * (C - X), "2*Y*(C-X)"),
        (
            "d3^2",
            2 * ((A + B) * (A + B - X) + Y * (A + B + C - X)),
            "2*((A+B)*(A+B-X) + Y*(A+B+C-X))",
        ),
        (
            "d3^2",
            2 * ((A + B) * (A + B - Y) + X * (A + B + C - Y)),
            "2*((A+B)*(A+B-Y) + X*(A+B+C-Y))",
        ),
        ("d5^2", 4 * X * (A + C), "4*X*(A+C)"),
        ("d3^2", 2 * C * (X + Y), "2*C*(X+Y)"),
        (
            "d3^2",
            2 * ((A + B) ** 2 + (A + B + C) * (X + Y)),
            "2*((A+B)^2 + (A+B+C)*(X+Y))",
        ),
        ("d3^2", 2 * X * (C - Y), "2*X*(C-Y)"),
        ("d4^2", 4 * Y * (B + C), "4*Y*(B+C)"),
    )

    extras: list[DiameterExtra] = []
    used_patterns: set[int] = set()
    for expression in sorted(expressions, key=str):
        if expression in canonical.values():
            continue
        match: tuple[int, str, sp.Expr, str] | None = None
        for pattern_index, (name, expected_gap, gap_display) in enumerate(target_gaps):
            if pattern_index in used_patterns:
                continue
            gap = sp.factor(
                (expression - canonical[name]).subs(xy_substitution)
            )
            if sp.simplify(gap - expected_gap) == 0:
                match = (pattern_index, name, sp.factor(expected_gap), gap_display)
                break
        if match is None:
            raise AssertionError(("unmatched diameter net", expression))
        pattern_index, name, gap, gap_display = match
        used_patterns.add(pattern_index)
        extras.append(
            DiameterExtra(
                chains=tuple(expressions[expression]),
                squared_length=sp.factor(expression),
                canonical_name=name,
                gap=gap,
                gap_display=gap_display,
            )
        )

    if len(paths) != 28 or len(expressions) != 14 or len(extras) != 9:
        raise AssertionError((len(paths), len(expressions), len(extras)))
    if len(used_patterns) != 9:
        raise AssertionError(used_patterns)
    return paths, canonical, extras


def format_path(path: tuple[str, ...]) -> str:
    return " -> ".join(path)


def main() -> None:
    fixed_paths, fixed_images, dominations = audit_fixed_vertex()
    diameter_paths, canonical, extras = audit_diameter()

    print("CUBOID UNFOLDING AUDIT: PASS")
    print()
    print("FIXED VERTEX TO TOP FACE")
    print(f"  simple face chains enumerated: {len(fixed_paths)}")
    print(f"  distinct planar source images: {len(fixed_images)}")
    print("  canonical sources:")
    print("    S1 = (-C, 0)")
    print("    S2 = (A+C, -A)")
    print("    S3 = (0, -C)")
    print("    S4 = (-B, B+C)")
    print(f"  noncanonical images dominated: {len(dominations)}")
    print()
    print("  Corner-certificate convention:")
    print("    B=A+U, C=A+U+V with A>0 and U,V>=0.")
    print("    The four entries are extra-distance^2 minus canonical-distance^2")
    print("    at (0,0), (A,0), (0,B), (A,B).  Every displayed polynomial")
    print("    has nonnegative coefficients, so it is nonnegative.")
    print()
    for item in dominations:
        print(f"  source {item.source} is dominated by S{item.canonical_index}")
        for corner_name, certificate in zip(
            ("(0,0)", "(A,0)", "(0,B)", "(A,B)"),
            item.corner_certificates,
        ):
            print(f"    {corner_name}: {sp.sstr(certificate)}")
    print()

    print("ANTIPODAL BASE-TO-TOP PAIR")
    print(f"  simple face chains enumerated: {len(diameter_paths)}")
    print(f"  distinct squared net lengths: {len(canonical) + len(extras)}")
    print("  five canonical lengths retained: d1^2,...,d5^2")
    print("  Set X=A-2x and Y=B-2y; then 0<=X<=A and 0<=Y<=B.")
    print("  Each noncanonical net is dominated as follows:")
    print()
    for index, item in enumerate(extras, start=1):
        print(f"  e{index} chains:")
        for path in item.chains:
            print(f"    {format_path(path)}")
        print(f"    e{index} = {sp.sstr(item.squared_length)}")
        print(f"    e{index} - {item.canonical_name} = {item.gap_display} >= 0")
    print()
    print("All finite unfolding classifications used in the report passed.")


if __name__ == "__main__":
    main()
