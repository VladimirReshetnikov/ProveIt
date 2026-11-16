#!/usr/bin/env python3
"""Exact finite reference kernel for the PL Conway criterion.

This module is deliberately small and uses only Python's standard library.
Coordinates are rational (`fractions.Fraction`).  It checks the local Conway
boundary equations, derives the two period vectors, verifies the exact
shoelace identity

    det(t, u) = twice_area(tile),

and, for a concrete polygon, certifies the two-orbit construction on the
period torus by exact rational clipping:

* triangulate the tile;
* project both orbit representatives to lattice coordinates;
* cut all translated triangles by the unit fundamental square;
* check that the resulting closed convex pieces have pairwise zero-area
  intersections and total area one.

The executable is a reference implementation, not an iPRA proof checker.  The
paper proves why the checks succeed for every valid PL Conway datum and explains
how these finite algorithms are represented by primitive-recursive symbols.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import argparse
import json
import math
from pathlib import Path as FsPath
from typing import Any, Iterable, Iterator, Mapping, Sequence

Q = Fraction
Point = tuple[Q, Q]
Path = tuple[Point, ...]
Polygon = tuple[Point, ...]
Triangle = tuple[Point, Point, Point]


class ConwayError(ValueError):
    """Raised when a finite datum fails a required exact check."""


def q(value: Any) -> Q:
    """Parse an integer, rational string, [numerator, denominator], or Fraction."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Q(value)
    if isinstance(value, str):
        return Q(value)
    if isinstance(value, (list, tuple)) and len(value) == 2:
        return Q(int(value[0]), int(value[1]))
    raise TypeError(f"cannot parse rational value {value!r}")


def point(value: Sequence[Any]) -> Point:
    if len(value) != 2:
        raise TypeError(f"point must have two coordinates: {value!r}")
    return q(value[0]), q(value[1])


def p_add(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def p_sub(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def p_scale(c: Q, a: Point) -> Point:
    return c * a[0], c * a[1]


def det(a: Point, b: Point) -> Q:
    return a[0] * b[1] - a[1] * b[0]


def orient(a: Point, b: Point, c: Point) -> Q:
    return det(p_sub(b, a), p_sub(c, a))


def translate_point(a: Point, w: Point) -> Point:
    return p_add(a, w)


def halfturn_point(a: Point, doubled_center: Point) -> Point:
    """The half-turn x |-> 2m-x, supplied with doubled center 2m."""
    return p_sub(doubled_center, a)


def translate_path(path: Path, w: Point) -> Path:
    return tuple(translate_point(a, w) for a in path)


def halfturn_path(path: Path, doubled_center: Point) -> Path:
    return tuple(halfturn_point(a, doubled_center) for a in path)


def reverse_path(path: Path) -> Path:
    return tuple(reversed(path))


def remove_consecutive_duplicates(points: Sequence[Point], *, cyclic: bool = False) -> list[Point]:
    out: list[Point] = []
    for p in points:
        if not out or p != out[-1]:
            out.append(p)
    if cyclic and len(out) > 1 and out[0] == out[-1]:
        out.pop()
    return out


def between(a: Point, b: Point, c: Point) -> bool:
    """Whether b lies on the closed segment ac (assuming collinearity)."""
    return (
        min(a[0], c[0]) <= b[0] <= max(a[0], c[0])
        and min(a[1], c[1]) <= b[1] <= max(a[1], c[1])
    )


def canonical_path(path: Sequence[Point]) -> Path:
    """Remove duplicate and redundant collinear subdivision vertices."""
    pts = remove_consecutive_duplicates(path)
    if len(pts) <= 2:
        return tuple(pts)
    changed = True
    while changed and len(pts) > 2:
        changed = False
        out = [pts[0]]
        for i in range(1, len(pts) - 1):
            a, b, c = out[-1], pts[i], pts[i + 1]
            if orient(a, b, c) == 0 and between(a, b, c):
                changed = True
            else:
                out.append(b)
        out.append(pts[-1])
        pts = out
    return tuple(pts)


def paths_equal(a: Sequence[Point], b: Sequence[Point]) -> bool:
    return canonical_path(a) == canonical_path(b)


def path_J(path: Sequence[Point]) -> Q:
    """The open-path shoelace functional sum det(p_i,p_{i+1})."""
    return sum((det(a, b) for a, b in zip(path, path[1:])), Q(0))


def polygon_area2(poly: Sequence[Point]) -> Q:
    """Twice oriented area of a cyclic polygon."""
    if len(poly) < 3:
        return Q(0)
    return sum((det(poly[i], poly[(i + 1) % len(poly)]) for i in range(len(poly))), Q(0))


def on_segment(a: Point, b: Point, p: Point) -> bool:
    return orient(a, b, p) == 0 and between(a, p, b)


def segments_intersect(a: Point, b: Point, c: Point, d: Point) -> bool:
    o1, o2, o3, o4 = orient(a, b, c), orient(a, b, d), orient(c, d, a), orient(c, d, b)
    if o1 == 0 and on_segment(a, b, c):
        return True
    if o2 == 0 and on_segment(a, b, d):
        return True
    if o3 == 0 and on_segment(c, d, a):
        return True
    if o4 == 0 and on_segment(c, d, b):
        return True
    return (o1 > 0) != (o2 > 0) and (o3 > 0) != (o4 > 0)


def simplify_polygon(poly: Sequence[Point]) -> Polygon:
    pts = remove_consecutive_duplicates(poly, cyclic=True)
    if len(pts) < 3:
        return tuple(pts)
    changed = True
    while changed and len(pts) > 3:
        changed = False
        out: list[Point] = []
        n = len(pts)
        for i, b in enumerate(pts):
            a, c = pts[(i - 1) % n], pts[(i + 1) % n]
            if orient(a, b, c) == 0 and between(a, b, c):
                changed = True
            else:
                out.append(b)
        pts = out
    return tuple(pts)


def is_simple_polygon(poly: Sequence[Point]) -> bool:
    pts = simplify_polygon(poly)
    n = len(pts)
    if n < 3 or len(set(pts)) != n:
        return False
    for i in range(n):
        a, b = pts[i], pts[(i + 1) % n]
        if a == b:
            return False
        for j in range(i + 1, n):
            c, d = pts[j], pts[(j + 1) % n]
            # Adjacent edges are allowed to meet only at their common endpoint.
            if j == i or (j + 1) % n == i or (i + 1) % n == j:
                continue
            if segments_intersect(a, b, c, d):
                return False
    return True


def point_in_ccw_triangle(p: Point, a: Point, b: Point, c: Point) -> bool:
    return orient(a, b, p) >= 0 and orient(b, c, p) >= 0 and orient(c, a, p) >= 0


def triangulate(poly: Sequence[Point]) -> tuple[Triangle, ...]:
    """Exact ear clipping for a simple, positively oriented polygon."""
    pts = list(simplify_polygon(poly))
    if len(pts) < 3:
        raise ConwayError("polygon has fewer than three effective vertices")
    if polygon_area2(pts) < 0:
        pts.reverse()
    if polygon_area2(pts) == 0 or not is_simple_polygon(pts):
        raise ConwayError("ear clipping requires a simple nondegenerate polygon")

    indices = list(range(len(pts)))
    triangles: list[Triangle] = []
    guard = len(indices) * len(indices) + 1
    while len(indices) > 3:
        ear_found = False
        m = len(indices)
        for k in range(m):
            i0, i1, i2 = indices[(k - 1) % m], indices[k], indices[(k + 1) % m]
            a, b, c = pts[i0], pts[i1], pts[i2]
            if orient(a, b, c) <= 0:
                continue
            if any(
                point_in_ccw_triangle(pts[j], a, b, c)
                for j in indices
                if j not in (i0, i1, i2)
            ):
                continue
            triangles.append((a, b, c))
            del indices[k]
            ear_found = True
            break
        if not ear_found:
            raise ConwayError("ear clipping stalled (degeneracy or non-simple polygon)")
        guard -= 1
        if guard <= 0:
            raise ConwayError("ear clipping guard exhausted")
    a, b, c = (pts[i] for i in indices)
    if orient(a, b, c) <= 0:
        raise ConwayError("final ear is degenerate")
    triangles.append((a, b, c))
    return tuple(triangles)


def _dedup_polygon(poly: Sequence[Point]) -> Polygon:
    pts = remove_consecutive_duplicates(poly, cyclic=True)
    return tuple(pts)


def _clip_by_value(poly: Sequence[Point], value, *, keep_nonnegative: bool = True) -> Polygon:
    """Clip a convex polygon by an affine half-plane value(p)>=0 (or <=0)."""
    if not poly:
        return ()
    out: list[Point] = []
    s = poly[-1]
    vs = value(s)
    ins_s = vs >= 0 if keep_nonnegative else vs <= 0
    for e in poly:
        ve = value(e)
        ins_e = ve >= 0 if keep_nonnegative else ve <= 0
        if ins_e:
            if not ins_s:
                lam = vs / (vs - ve)
                out.append(p_add(s, p_scale(lam, p_sub(e, s))))
            out.append(e)
        elif ins_s:
            lam = vs / (vs - ve)
            out.append(p_add(s, p_scale(lam, p_sub(e, s))))
        s, vs, ins_s = e, ve, ins_e
    return _dedup_polygon(out)


def clip_to_unit_square(poly: Sequence[Point]) -> Polygon:
    out: Polygon = tuple(poly)
    out = _clip_by_value(out, lambda p: p[0])
    out = _clip_by_value(out, lambda p: Q(1) - p[0])
    out = _clip_by_value(out, lambda p: p[1])
    out = _clip_by_value(out, lambda p: Q(1) - p[1])
    if len(out) >= 3 and polygon_area2(out) < 0:
        out = tuple(reversed(out))
    return out


def line_intersection_by_orient(s: Point, e: Point, a: Point, b: Point) -> Point:
    ds, de = orient(a, b, s), orient(a, b, e)
    if ds == de:
        raise ConwayError("parallel segment presented as a clipping crossing")
    lam = ds / (ds - de)
    return p_add(s, p_scale(lam, p_sub(e, s)))


def convex_intersection(subject: Sequence[Point], clipper: Sequence[Point]) -> Polygon:
    out: Polygon = tuple(subject)
    cp = tuple(clipper)
    if len(out) < 3 or len(cp) < 3:
        return ()
    if polygon_area2(cp) < 0:
        cp = tuple(reversed(cp))
    for i in range(len(cp)):
        a, b = cp[i], cp[(i + 1) % len(cp)]
        if not out:
            break
        new: list[Point] = []
        s = out[-1]
        ds = orient(a, b, s)
        ins_s = ds >= 0
        for e in out:
            de = orient(a, b, e)
            ins_e = de >= 0
            if ins_e:
                if not ins_s:
                    new.append(line_intersection_by_orient(s, e, a, b))
                new.append(e)
            elif ins_s:
                new.append(line_intersection_by_orient(s, e, a, b))
            s, ds, ins_s = e, de, ins_e
        out = _dedup_polygon(new)
    if len(out) >= 3 and polygon_area2(out) < 0:
        out = tuple(reversed(out))
    return out


def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def floor_q(x: Q) -> int:
    return x.numerator // x.denominator


def lattice_coordinates(p: Point, t: Point, u: Point) -> Point:
    delta = det(t, u)
    if delta == 0:
        raise ConwayError("degenerate lattice")
    return det(p, u) / delta, det(t, p) / delta


def shifted_clipped_copies(convex_poly: Sequence[Point]) -> Iterator[Polygon]:
    xs = [p[0] for p in convex_poly]
    ys = [p[1] for p in convex_poly]
    ilo, ihi = ceil_q(-max(xs)), floor_q(Q(1) - min(xs))
    jlo, jhi = ceil_q(-max(ys)), floor_q(Q(1) - min(ys))
    for i in range(ilo, ihi + 1):
        for j in range(jlo, jhi + 1):
            shifted = tuple((p[0] + i, p[1] + j) for p in convex_poly)
            piece = clip_to_unit_square(shifted)
            if len(piece) >= 3 and abs(polygon_area2(piece)) > 0:
                yield piece


@dataclass(frozen=True)
class ConwayDatum:
    a: Path
    b: Path
    c: Path
    d: Path
    e: Path
    f: Path
    name: str = "unnamed"

    @staticmethod
    def from_mapping(obj: Mapping[str, Any]) -> "ConwayDatum":
        def get_path(k: str) -> Path:
            raw = obj[k]
            pts = tuple(point(v) for v in raw)
            if not pts:
                raise ConwayError(f"path {k} is empty as a list; use a singleton for an empty arc")
            return pts

        return ConwayDatum(
            a=get_path("a"), b=get_path("b"), c=get_path("c"),
            d=get_path("d"), e=get_path("e"), f=get_path("f"),
            name=str(obj.get("name", "unnamed")),
        )

    @property
    def A(self) -> Point:
        return self.a[0]

    @property
    def B(self) -> Point:
        return self.a[-1]

    @property
    def C(self) -> Point:
        return self.b[-1]

    @property
    def D(self) -> Point:
        return self.c[-1]

    @property
    def E(self) -> Point:
        return self.d[-1]

    @property
    def F(self) -> Point:
        return self.e[-1]

    @property
    def marked(self) -> tuple[Point, ...]:
        return self.A, self.B, self.C, self.D, self.E, self.F

    @property
    def t(self) -> Point:
        return p_sub(self.E, self.A)

    @property
    def u(self) -> Point:
        return p_sub(p_add(self.E, self.F), p_add(self.B, self.C))

    @property
    def e_center2(self) -> Point:
        return p_add(self.E, self.F)

    def paths(self) -> tuple[Path, ...]:
        return self.a, self.b, self.c, self.d, self.e, self.f

    def endpoint_errors(self) -> list[str]:
        p = self.paths()
        names = "abcdef"
        errors: list[str] = []
        for i in range(6):
            if p[i][-1] != p[(i + 1) % 6][0]:
                errors.append(f"path {names[i]} does not meet path {names[(i+1)%6]}")
        return errors

    def boundary_polygon(self) -> Polygon:
        if self.endpoint_errors():
            raise ConwayError("boundary paths are not cyclically consecutive")
        pts: list[Point] = []
        for i, path in enumerate(self.paths()):
            pts.extend(path if i == 0 else path[1:])
        if pts and pts[-1] == pts[0]:
            pts.pop()
        return tuple(remove_consecutive_duplicates(pts, cyclic=True))

    def local_checks(self) -> dict[str, bool]:
        continuity = not self.endpoint_errors()
        if not continuity:
            return {"continuity": False}
        poly = self.boundary_polygon()
        t = self.t
        checks = {
            "continuity": True,
            "at_least_three_marked_points": len(set(self.marked)) >= 3,
            "simple_boundary": is_simple_polygon(poly),
            "positive_orientation": polygon_area2(poly) > 0,
            "a_d_translation": paths_equal(translate_path(self.a, t), reverse_path(self.d)),
            "b_halfturn": paths_equal(halfturn_path(self.b, p_add(self.B, self.C)), reverse_path(self.b)),
            "c_halfturn": paths_equal(halfturn_path(self.c, p_add(self.C, self.D)), reverse_path(self.c)),
            "e_halfturn": paths_equal(halfturn_path(self.e, p_add(self.E, self.F)), reverse_path(self.e)),
            "f_halfturn": paths_equal(halfturn_path(self.f, p_add(self.F, self.A)), reverse_path(self.f)),
        }
        return checks

    def require_local_checks(self) -> None:
        checks = self.local_checks()
        failed = [k for k, ok in checks.items() if not ok]
        if failed:
            raise ConwayError("failed local Conway checks: " + ", ".join(failed))

    def doubled_area(self) -> Q:
        return polygon_area2(self.boundary_polygon())

    def path_shoelace_sum(self) -> Q:
        return sum((path_J(p) for p in self.paths()), Q(0))

    def area_identity(self) -> bool:
        return self.doubled_area() == self.path_shoelace_sum() == det(self.t, self.u)

    def orbit_boundary_identities(self) -> dict[str, bool]:
        s = self.e_center2
        t, u = self.t, self.u
        return {
            "H_e(b)=-T_u(b)": paths_equal(halfturn_path(self.b, s), reverse_path(translate_path(self.b, u))),
            "H_e(c)=-T_(u-t)(c)": paths_equal(
                halfturn_path(self.c, s), reverse_path(translate_path(self.c, p_sub(u, t)))
            ),
            "H_e(e)=-e": paths_equal(halfturn_path(self.e, s), reverse_path(self.e)),
            "H_e(f)=-T_t(f)": paths_equal(halfturn_path(self.f, s), reverse_path(translate_path(self.f, t))),
        }

    def torus_pieces(self) -> tuple[Polygon, ...]:
        self.require_local_checks()
        if not self.area_identity():
            raise ConwayError("derived determinant/area identity failed")
        t, u, s = self.t, self.u, self.e_center2
        if det(t, u) <= 0:
            raise ConwayError("period lattice is not positively oriented")
        triangles = triangulate(self.boundary_polygon())
        reps: list[Triangle] = list(triangles)
        reps.extend(tuple(halfturn_point(p, s) for p in tri) for tri in triangles)
        pieces: list[Polygon] = []
        for tri in reps:
            ltri = tuple(lattice_coordinates(p, t, u) for p in tri)
            if polygon_area2(ltri) < 0:
                ltri = tuple(reversed(ltri))
            pieces.extend(shifted_clipped_copies(ltri))
        return tuple(pieces)

    def torus_certificate(self) -> dict[str, Any]:
        pieces = self.torus_pieces()
        total_area2 = sum((abs(polygon_area2(p)) for p in pieces), Q(0))
        overlap_pairs: list[tuple[int, int, Q]] = []
        max_overlap2 = Q(0)
        for (i, a), (j, b) in combinations(enumerate(pieces), 2):
            inter = convex_intersection(a, b)
            area2 = abs(polygon_area2(inter)) if len(inter) >= 3 else Q(0)
            if area2 > 0:
                overlap_pairs.append((i, j, area2))
                max_overlap2 = max(max_overlap2, area2)
        inside = all(
            Q(0) <= x <= Q(1) and Q(0) <= y <= Q(1)
            for poly in pieces for x, y in poly
        )
        exact = inside and total_area2 == 2 and not overlap_pairs
        return {
            "piece_count": len(pieces),
            "total_area": total_area2 / 2,
            "max_pairwise_overlap_area": max_overlap2 / 2,
            "positive_overlap_pair_count": len(overlap_pairs),
            "all_pieces_in_unit_square": inside,
            "exact_multiplicity_one": exact,
        }

    def report(self, *, include_torus: bool = True) -> dict[str, Any]:
        checks = self.local_checks()
        result: dict[str, Any] = {
            "name": self.name,
            "local_checks": checks,
            "local_conway_ok": all(checks.values()),
            "marked_points": [point_json(p) for p in self.marked],
            "period_t": point_json(self.t),
            "period_u": point_json(self.u),
            "det_t_u": rational_json(det(self.t, self.u)),
            "twice_area": rational_json(self.doubled_area()) if checks.get("continuity") else None,
            "area_identity": self.area_identity() if all(checks.values()) else False,
            "orbit_boundary_identities": self.orbit_boundary_identities() if all(checks.values()) else {},
            "base_tile_adjacency": {
                "a": "type0(n-1,k):d",
                "d": "type0(n+1,k):a",
                "b": "type1(n,k-1):b",
                "c": "type1(n+1,k-1):c",
                "e": "type1(n,k):e",
                "f": "type1(n-1,k):f",
            },
        }
        if include_torus and all(checks.values()):
            result["torus_certificate"] = jsonable(self.torus_certificate())
        return result


def rational_json(x: Q) -> int | str:
    return x.numerator if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def point_json(p: Point) -> list[int | str]:
    return [rational_json(p[0]), rational_json(p[1])]


def jsonable(value: Any) -> Any:
    if isinstance(value, Fraction):
        return rational_json(value)
    if isinstance(value, tuple):
        return [jsonable(v) for v in value]
    if isinstance(value, list):
        return [jsonable(v) for v in value]
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    return value


def load_datum(path: FsPath) -> ConwayDatum:
    with path.open("r", encoding="utf-8") as fh:
        return ConwayDatum.from_mapping(json.load(fh))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=FsPath, help="JSON Conway datum")
    parser.add_argument("--no-torus", action="store_true", help="skip exact torus clipping certificate")
    parser.add_argument("--output", type=FsPath, help="write JSON report here")
    args = parser.parse_args(argv)
    datum = load_datum(args.input)
    report = datum.report(include_torus=not args.no_torus)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if report["local_conway_ok"] and (args.no_torus or report["torus_certificate"]["exact_multiplicity_one"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
