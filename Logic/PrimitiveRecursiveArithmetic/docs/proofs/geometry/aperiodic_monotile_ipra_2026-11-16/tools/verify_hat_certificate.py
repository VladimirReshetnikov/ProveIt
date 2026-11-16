#!/usr/bin/env python3
"""Exact-arithmetic reference verifier for the iPRA hat packet.

This is deliberately small and transparent.  Coordinates are represented in the
basis (x, yhat), where the Euclidean point is (x, sqrt(3)*yhat); consequently all
coordinates and affine matrices used by the hatviz metatile construction are
rational.  The program checks:

* the 13-vertex hat polygon is simple and has area 8*sqrt(3);
* the fixed 29-entry metatile patch has the advertised type counts;
* the four supertile selections give the advertised substitution matrix;
* the characteristic polynomial is x^4-7x^3+7x-1;
* the triangular norm Q(m,n)=m^2+mn+n^2 is even only when m,n are even;
* six exact generations of the hatviz construction have convex H outlines and
  contain the distinguished H child strictly in their interiors.

The finite-generation geometry check is evidence and a regression test.  The
unbounded-growth proof is mathematical (see the report); it is not inferred by
extrapolating these six rows.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
from collections import Counter
from dataclasses import dataclass, field
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable, Sequence

Point = tuple[F, F]              # (x, yhat), Euclidean y = sqrt(3)*yhat
Matrix = tuple[tuple[F, F, F], tuple[F, F, F], tuple[F, F, F]]

I: Matrix = ((F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1)))


def p(x: int | F = 0, y: int | F = 0) -> Point:
    return F(x), F(y)


def padd(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def psub(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def cross(a: Point, b: Point) -> F:
    # Euclidean determinant is sqrt(3) times this rational number.
    return a[0] * b[1] - a[1] * b[0]


def mmul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


def minv(a: Matrix) -> Matrix:
    aa, bb, tx = a[0]
    cc, dd, ty = a[1]
    det = aa * dd - bb * cc
    if det == 0:
        raise ValueError("singular affine matrix")
    return (
        (dd / det, -bb / det, (bb * ty - dd * tx) / det),
        (-cc / det, aa / det, (cc * tx - aa * ty) / det),
        (F(0), F(0), F(1)),
    )


def mpoint(a: Matrix, q: Point) -> Point:
    return (
        a[0][0] * q[0] + a[0][1] * q[1] + a[0][2],
        a[1][0] * q[0] + a[1][1] * q[1] + a[1][2],
    )


def translation(tx: F | int, ty: F | int) -> Matrix:
    return ((F(1), F(0), F(tx)), (F(0), F(1), F(ty)), (F(0), F(0), F(1)))


# Rotation by k*pi/3 in rational (x,yhat) coordinates.
ROT: dict[int, Matrix] = {
    0: I,
    1: ((F(1, 2), F(-3, 2), F(0)), (F(1, 2), F(1, 2), F(0)), (F(0), F(0), F(1))),
    -1: ((F(1, 2), F(3, 2), F(0)), (F(-1, 2), F(1, 2), F(0)), (F(0), F(0), F(1))),
    2: ((F(-1, 2), F(-3, 2), F(0)), (F(1, 2), F(-1, 2), F(0)), (F(0), F(0), F(1))),
    -2: ((F(-1, 2), F(3, 2), F(0)), (F(-1, 2), F(-1, 2), F(0)), (F(0), F(0), F(1))),
    3: ((F(-1), F(0), F(0)), (F(0), F(-1), F(0)), (F(0), F(0), F(1))),
    -3: ((F(-1), F(0), F(0)), (F(0), F(-1), F(0)), (F(0), F(0), F(1))),
}


def rot_about(q: Point, k: int) -> Matrix:
    return mmul(translation(*q), mmul(ROT[k], translation(-q[0], -q[1])))


def match_segment(a: Point, b: Point) -> Matrix:
    """Map the Euclidean unit segment to a->b, in rational coordinates."""
    dx = b[0] - a[0]
    dyhat = b[1] - a[1]
    return ((dx, -3 * dyhat, a[0]), (dyhat, dx, a[1]), (F(0), F(0), F(1)))


def match_two(a: Point, b: Point, c: Point, d: Point) -> Matrix:
    return mmul(match_segment(c, d), minv(match_segment(a, b)))


def line_intersection(a: Point, b: Point, c: Point, d: Point) -> Point:
    dx1, dy1 = b[0] - a[0], b[1] - a[1]
    dx2, dy2 = d[0] - c[0], d[1] - c[1]
    den = dy2 * dx1 - dx2 * dy1
    if den == 0:
        raise ValueError("parallel lines")
    u = (dx2 * (a[1] - c[1]) - dy2 * (a[0] - c[0])) / den
    return a[0] + u * dx1, a[1] + u * dy1


def axial(u: int | F, v: int | F) -> Point:
    # (u,v) -> (u+v/2, sqrt(3)*v/2)
    return F(u) + F(v, 2), F(v, 2)


def shoelace(points: Sequence[tuple[int, int]]) -> int:
    return sum(
        points[i][0] * points[(i + 1) % len(points)][1]
        - points[(i + 1) % len(points)][0] * points[i][1]
        for i in range(len(points))
    )


def orient(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def on_segment(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> bool:
    return (
        orient(a, b, c) == 0
        and min(a[0], b[0]) <= c[0] <= max(a[0], b[0])
        and min(a[1], b[1]) <= c[1] <= max(a[1], b[1])
    )


def segments_intersect(a, b, c, d) -> bool:
    o1, o2, o3, o4 = orient(a, b, c), orient(a, b, d), orient(c, d, a), orient(c, d, b)
    if (o1 > 0 > o2 or o2 > 0 > o1) and (o3 > 0 > o4 or o4 > 0 > o3):
        return True
    return any((on_segment(a, b, c), on_segment(a, b, d), on_segment(c, d, a), on_segment(c, d, b)))


def polygon_is_simple(points: Sequence[tuple[int, int]]) -> bool:
    n = len(points)
    for i in range(n):
        a, b = points[i], points[(i + 1) % n]
        for j in range(i + 1, n):
            if j in (i, (i + 1) % n) or i in (j, (j + 1) % n):
                continue
            if i == 0 and j == n - 1:
                continue
            c, d = points[j], points[(j + 1) % n]
            if segments_intersect(a, b, c, d):
                return False
    return True


@dataclass
class Geom:
    shape: list[Point]
    children: list[tuple[Matrix, "Geom"]] = field(default_factory=list)
    label: str = ""
    width: int = 2

    def add(self, transform: Matrix, child: "Geom") -> None:
        self.children.append((transform, child))

    def eval_child(self, child: int, vertex: int) -> Point:
        t, g = self.children[child]
        return mpoint(t, g.shape[vertex])

    def recenter(self) -> None:
        n = F(len(self.shape))
        cx = sum(q[0] for q in self.shape) / n
        cy = sum(q[1] for q in self.shape) / n
        self.shape = [(q[0] - cx, q[1] - cy) for q in self.shape]
        shift = translation(-cx, -cy)
        self.children = [(mmul(shift, t), g) for t, g in self.children]


PATCH_RULES: list[list[object]] = [
    ["H"],
    [0, 0, "P", 2], [1, 0, "H", 2], [2, 0, "P", 2], [3, 0, "H", 2],
    [4, 4, "P", 2], [0, 4, "F", 3], [2, 4, "F", 3],
    [4, 1, 3, 2, "F", 0], [8, 3, "H", 0], [9, 2, "P", 0], [10, 2, "H", 0],
    [11, 4, "P", 2], [12, 0, "H", 2], [13, 0, "F", 3], [14, 2, "F", 1],
    [15, 3, "H", 4], [8, 2, "F", 1], [17, 3, "H", 0], [18, 2, "P", 0],
    [19, 2, "H", 2], [20, 4, "F", 3], [20, 0, "P", 2], [22, 0, "H", 2],
    [23, 4, "F", 3], [23, 0, "F", 3], [16, 0, "P", 2],
    [9, 4, 0, 2, "T", 2], [4, 0, "F", 3],
]

SELECT = {
    "H": [0, 9, 16, 27, 26, 6, 1, 8, 10, 15],
    "T": [11],
    "P": [7, 2, 3, 4, 28],
    "F": [21, 20, 22, 23, 24, 25],
}


def initial_geometries(hat_axial: Sequence[tuple[int, int]]) -> list[Geom]:
    hat = [axial(u, v) for u, v in hat_axial]
    leaves = {name: Geom(hat.copy(), label=name) for name in ("H", "H1", "T", "P", "F")}

    hs = [p(0, 0), p(4, 0), p(F(9, 2), F(1, 2)), p(F(5, 2), F(5, 2)), p(F(3, 2), F(5, 2)), p(F(-1, 2), F(1, 2))]
    h = Geom(hs)
    h.add(match_two(hat[5], hat[7], hs[5], hs[0]), leaves["H"])
    h.add(match_two(hat[9], hat[11], hs[1], hs[2]), leaves["H"])
    h.add(match_two(hat[5], hat[7], hs[3], hs[4]), leaves["H"])
    reflect_scale: Matrix = ((F(1, 2), F(0), F(0)), (F(0), F(-1, 2), F(0)), (F(0), F(0), F(1)))
    h.add(mmul(translation(F(5, 2), F(1, 2)), mmul(ROT[2], reflect_scale)), leaves["H1"])

    ts = [p(0, 0), p(3, 0), p(F(3, 2), F(3, 2))]
    t = Geom(ts)
    t.add(((F(1, 2), F(0), F(1, 2)), (F(0), F(1, 2), F(1, 2)), (F(0), F(0), F(1))), leaves["T"])

    ps = [p(0, 0), p(4, 0), p(3, 1), p(-1, 1)]
    pgeom = Geom(ps)
    pgeom.add(((F(1, 2), F(0), F(3, 2)), (F(0), F(1, 2), F(1, 2)), (F(0), F(0), F(1))), leaves["P"])
    half: Matrix = ((F(1, 2), F(0), F(0)), (F(0), F(1, 2), F(0)), (F(0), F(0), F(1)))
    pgeom.add(mmul(translation(0, 1), mmul(ROT[-1], half)), leaves["P"])

    fs = [p(0, 0), p(3, 0), p(F(7, 2), F(1, 2)), p(3, 1), p(-1, 1)]
    fgeom = Geom(fs)
    fgeom.add(((F(1, 2), F(0), F(3, 2)), (F(0), F(1, 2), F(1, 2)), (F(0), F(0), F(1))), leaves["F"])
    fgeom.add(mmul(translation(0, 1), mmul(ROT[-1], half)), leaves["F"])
    return [h, t, pgeom, fgeom]


def construct_patch(tiles: Sequence[Geom]) -> tuple[Geom, list[str]]:
    names = dict(zip(("H", "T", "P", "F"), tiles, strict=True))
    result = Geom([])
    types: list[str] = []
    for rule in PATCH_RULES:
        if len(rule) == 1:
            name = str(rule[0])
            result.add(I, names[name])
            types.append(name)
        elif len(rule) == 4:
            source, edge, name, new_edge = int(rule[0]), int(rule[1]), str(rule[2]), int(rule[3])
            tr, geom = result.children[source]
            a = mpoint(tr, geom.shape[(edge + 1) % len(geom.shape)])
            b = mpoint(tr, geom.shape[edge])
            new = names[name]
            result.add(match_two(new.shape[new_edge], new.shape[(new_edge + 1) % len(new.shape)], a, b), new)
            types.append(name)
        else:
            pidx, pvert, qidx, qvert, name, new_edge = (
                int(rule[0]), int(rule[1]), int(rule[2]), int(rule[3]), str(rule[4]), int(rule[5])
            )
            tp, gp = result.children[pidx]
            tq, gq = result.children[qidx]
            a = mpoint(tq, gq.shape[qvert])
            b = mpoint(tp, gp.shape[pvert])
            new = names[name]
            result.add(match_two(new.shape[new_edge], new.shape[(new_edge + 1) % len(new.shape)], a, b), new)
            types.append(name)
    return result, types


def construct_metatiles(patch: Geom) -> list[Geom]:
    bps1 = patch.eval_child(8, 2)
    bps2 = patch.eval_child(21, 2)
    rbps = mpoint(rot_about(bps1, -2), bps2)
    p72 = patch.eval_child(7, 2)
    p252 = patch.eval_child(25, 2)
    llc = line_intersection(bps1, rbps, patch.eval_child(6, 2), p72)

    w = psub(patch.eval_child(6, 2), llc)
    hout = [llc, bps1]
    w = mpoint(ROT[-1], w)
    hout.append(padd(hout[1], w))
    hout.append(patch.eval_child(14, 2))
    w = mpoint(ROT[-1], w)
    hout.append(psub(hout[3], w))
    hout.append(patch.eval_child(6, 2))
    new_h = Geom(hout, width=2 * patch.width)
    for idx in SELECT["H"]:
        new_h.add(*patch.children[idx])

    pout = [p72, padd(p72, psub(bps1, llc)), bps1, llc]
    new_p = Geom(pout, width=2 * patch.width)
    for idx in SELECT["P"]:
        new_p.add(*patch.children[idx])

    fout = [bps2, patch.eval_child(24, 2), patch.eval_child(25, 0), p252, padd(p252, psub(llc, bps1))]
    new_f = Geom(fout, width=2 * patch.width)
    for idx in SELECT["F"]:
        new_f.add(*patch.children[idx])

    aaa = hout[2]
    bbb = padd(hout[1], psub(hout[4], hout[5]))
    ccc = mpoint(rot_about(bbb, -1), aaa)
    new_t = Geom([bbb, ccc, aaa], width=2 * patch.width)
    new_t.add(*patch.children[11])

    for geom in (new_h, new_t, new_p, new_f):
        geom.recenter()
    return [new_h, new_t, new_p, new_f]


def convex_ccw(points: Sequence[Point]) -> bool:
    signs = []
    for i in range(len(points)):
        a, b, c = points[i], points[(i + 1) % len(points)], points[(i + 2) % len(points)]
        signs.append(cross(psub(b, a), psub(c, b)))
    return all(s > 0 for s in signs)


def child_edge_slacks(parent: Geom, child_index: int) -> list[F]:
    tr, child = parent.children[child_index]
    child_points = [mpoint(tr, q) for q in child.shape]
    answer: list[F] = []
    for i, a in enumerate(parent.shape):
        b = parent.shape[(i + 1) % len(parent.shape)]
        edge = psub(b, a)
        answer.append(min(cross(edge, psub(q, a)) for q in child_points))
    return answer


def permutation_sign(perm: Sequence[int]) -> int:
    inv = sum(1 for i in range(len(perm)) for j in range(i + 1, len(perm)) if perm[i] > perm[j])
    return -1 if inv % 2 else 1


def poly_add(a: list[int], b: list[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] += x
    for i, x in enumerate(b): out[i] += x
    return out


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def charpoly(matrix: Sequence[Sequence[int]]) -> list[int]:
    """Coefficients low-to-high of det(xI-M), by the Leibniz formula."""
    n = len(matrix)
    total = [0]
    for perm in itertools.permutations(range(n)):
        term = [permutation_sign(perm)]
        for i, j in enumerate(perm):
            factor = [-matrix[i][j], 1] if i == j else [-matrix[i][j]]
            term = poly_mul(term, factor)
        total = poly_add(total, term)
    while len(total) > 1 and total[-1] == 0:
        total.pop()
    return total


def qnorm(m: int, n: int) -> int:
    return m * m + m * n + n * n


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--levels", type=int, default=6)
    args = parser.parse_args()
    root: Path = args.root

    hat_data = json.loads((root / "certificates/hat_data.json").read_text())
    subst = json.loads((root / "certificates/substitution_rules.json").read_text())
    vertices = [tuple(map(int, q)) for q in hat_data["hat_vertices_axial"]]

    checks: dict[str, object] = {}
    checks["hat_simple"] = polygon_is_simple(vertices)
    checks["hat_shoelace"] = shoelace(vertices)
    assert checks["hat_simple"] is True
    assert checks["hat_shoelace"] == hat_data["expected_hat_shoelace"]

    # Recover child types from the fixed patch recipe.
    patch_types: list[str] = []
    for rule in PATCH_RULES:
        patch_types.append(str(rule[0]) if len(rule) == 1 else str(rule[2]) if len(rule) == 4 else str(rule[4]))
    checks["patch_type_counts"] = dict(Counter(patch_types))
    expected_counts = subst["expected_child_counts"]
    for parent, indices in SELECT.items():
        got = Counter(patch_types[i] for i in indices)
        want = Counter({k: int(v) for k, v in expected_counts[parent].items() if int(v) != 0})
        assert got == want, (parent, got, want)

    matrix = [[int(x) for x in row] for row in subst["substitution_matrix"]]
    cp = charpoly(matrix)
    checks["characteristic_polynomial_low_to_high"] = cp
    assert cp == [-1, 7, 0, -7, 1]

    parity_table = {(m, n): qnorm(m, n) % 2 for m in range(2) for n in range(2)}
    checks["triangular_norm_mod2"] = {f"{m}{n}": v for (m, n), v in parity_table.items()}
    assert parity_table == {(0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 1}

    tiles = initial_geometries(vertices)
    rows: list[dict[str, str | int | float]] = []
    previous_min: F | None = None
    for level in range(1, args.levels + 1):
        patch, types = construct_patch(tiles)
        assert Counter(types) == Counter({"H": 10, "T": 1, "P": 8, "F": 10})
        tiles = construct_metatiles(patch)
        h = tiles[0]
        assert convex_ccw(h.shape)
        slacks = child_edge_slacks(h, 0)
        min_slack = min(slacks)
        assert min_slack > 0
        if previous_min is not None:
            assert min_slack > 6 * previous_min
        previous_min = min_slack
        rows.append({
            "level": level,
            "minimum_exact_cross_slack": str(min_slack),
            "minimum_cross_slack_decimal": float(min_slack),
            "max_denominator_H_outline": max(q.denominator for point in h.shape for q in point),
            "H_children": len(h.children),
        })

    generated = root / "generated"
    generated.mkdir(exist_ok=True)
    with (generated / "exact_geometry_stats.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)

    checks["exact_geometry_levels"] = rows
    checks["status"] = "PASS"
    (generated / "verification_report.json").write_text(json.dumps(checks, indent=2) + "\n")

    print("PASS: exact hat and substitution certificate")
    print(f"  shoelace={checks['hat_shoelace']} -> area=8*sqrt(3)")
    print(f"  charpoly low-to-high={cp}")
    print(f"  exact metatile generations={args.levels}")
    print(f"  report={generated / 'verification_report.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
