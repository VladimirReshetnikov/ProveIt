#!/usr/bin/env python3
"""Independent numerical shortest paths on a rectangular box surface.

This is an unfolding calculation, not a triangulated-mesh approximation.
Every simple chain in the six-face adjacency graph is considered.  Each chain
is developed into the plane by reflecting successive faces across their common
edge.  A proposed straight segment is accepted only when it meets the actual
shared edge segments in the required order and stays in the respective faces.

Why simple chains suffice: if a shortest path leaves and later revisits a
convex face, replace the intervening excursion by the straight segment in that
face.  Its length cannot increase.  Repeating this gives a shortest path with
no face repeated.  Within a face it is straight; unfolding across an ordinary
edge makes consecutive pieces straight.  An interior passage through a box
vertex cannot be shortest because the total cone angle there is 3*pi/2 < 2*pi.
Paths on edges and endpoints at edges or vertices are handled by closed faces
and zero-length face intervals.

The enumeration is finite and complete in exact Euclidean arithmetic.  This
implementation uses binary floating point and tolerances, so its output is a
numerical check, not a formal certificate or an interval-arithmetic bound.
Coordinates are normalized by the largest side before arithmetic.  Inputs
within ``tol`` times that side of a boundary coordinate are snapped to it.
Very thin boxes or distinctions on the tolerance scale need higher precision.

Examples::

    python3 unfold_verify.py --sides 1 1 2 --p 0 0 0 --q .75 .75 2
    python3 unfold_verify.py --self-test

The public function ``surface_distance(sides, p, q)`` returns the distance;
``shortest_path`` also returns a face chain and its edge crossings.
Only the Python standard library is required.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
import math
from typing import Iterable, Iterator, Sequence

Vec2 = tuple[float, float]
Vec3 = tuple[float, float, float]
Face = tuple[int, int]  # coordinate axis, side 0 (lower) or 1 (upper)

FACES: tuple[Face, ...] = tuple((axis, side) for axis in range(3) for side in (0, 1))


def face_name(face: Face) -> str:
    return "xyz"[face[0]] + ("=0" if face[1] == 0 else "=max")


def add2(a: Vec2, b: Vec2) -> Vec2:
    return (a[0] + b[0], a[1] + b[1])


def sub2(a: Vec2, b: Vec2) -> Vec2:
    return (a[0] - b[0], a[1] - b[1])


def mul2(t: float, a: Vec2) -> Vec2:
    return (t * a[0], t * a[1])


def dot2(a: Vec2, b: Vec2) -> float:
    return a[0] * b[0] + a[1] * b[1]


def lerp2(p: Vec2, q: Vec2, t: float) -> Vec2:
    return add2(p, mul2(t, sub2(q, p)))


@dataclass(frozen=True)
class Chart:
    """Affine isometry of one face to the developed plane.

    The column for the face's fixed coordinate is zero.  The other two
    columns form a signed orthonormal coordinate basis of the plane.
    """

    face: Face
    columns: tuple[Vec2, Vec2, Vec2]
    offset: Vec2

    def project(self, p: Sequence[float]) -> Vec2:
        result = self.offset
        for i in range(3):
            result = add2(result, mul2(p[i], self.columns[i]))
        return result

    def lift(self, p: Vec2, sides: Vec3) -> Vec3:
        delta = sub2(p, self.offset)
        coordinates = [dot2(delta, column) for column in self.columns]
        coordinates[self.face[0]] = self.face[1] * sides[self.face[0]]
        return tuple(coordinates)  # type: ignore[return-value]


@dataclass(frozen=True)
class PathResult:
    distance: float
    face_chain: tuple[str, ...]
    crossing_points: tuple[Vec3, ...]
    crossing_parameters: tuple[float, ...]
    unfolded_start: Vec2
    unfolded_end: Vec2
    start: Vec3
    end: Vec3
    valid_chain_count: int
    minimizing_chain_count: int
    tolerance_relative_to_largest_side: float


@dataclass(frozen=True)
class _Candidate:
    distance: float  # normalized by largest side
    chain: tuple[Face, ...]
    charts: tuple[Chart, ...]
    times: tuple[float, ...]
    start2: Vec2
    end2: Vec2


def _as_vec3(value: Sequence[float], name: str) -> Vec3:
    if len(value) != 3:
        raise ValueError(f"{name} must have three coordinates")
    result = tuple(float(x) for x in value)
    if not all(math.isfinite(x) for x in result):
        raise ValueError(f"{name} must contain finite numbers")
    return result  # type: ignore[return-value]


def _normalize_input(
    sides: Sequence[float], p: Sequence[float], q: Sequence[float], tol: float
) -> tuple[Vec3, Vec3, Vec3, float]:
    dimensions = _as_vec3(sides, "sides")
    if min(dimensions) <= 0:
        raise ValueError("All three side lengths must be strictly positive")
    if not math.isfinite(tol) or tol < 0 or tol >= 0.01:
        raise ValueError("tol must be finite and satisfy 0 <= tol < 0.01")
    scale = max(dimensions)
    normalized = tuple(x / scale for x in dimensions)

    def normalize_point(point: Sequence[float], name: str) -> Vec3:
        point3 = _as_vec3(point, name)
        values: list[float] = []
        on_boundary = False
        for value, side in zip(point3, normalized):
            value /= scale
            if value < -tol or value > side + tol:
                raise ValueError(f"{name} is outside the box")
            low, high = abs(value), abs(value - side)
            if min(low, high) <= tol:
                value = 0.0 if low <= high else side
                on_boundary = True
            values.append(value)
        if not on_boundary:
            raise ValueError(f"{name} is not on the box surface")
        return tuple(values)  # type: ignore[return-value]

    return normalized, normalize_point(p, "p"), normalize_point(q, "q"), scale  # type: ignore[return-value]


def incident_faces(sides: Vec3, p: Vec3) -> tuple[Face, ...]:
    """Incident closed faces of an already normalized and snapped point."""
    return tuple(face for face in FACES if p[face[0]] == face[1] * sides[face[0]])


def simple_face_chains(
    starts: Iterable[Face], ends: Iterable[Face]
) -> Iterator[tuple[Face, ...]]:
    """All simple adjacency chains, including one-face cases.

    There is no length-zero chain: coincident points use a one-face chain.
    If an endpoint belongs to several faces, all its incident faces are used.
    """
    end_set = set(ends)

    def extend(chain: tuple[Face, ...]) -> Iterator[tuple[Face, ...]]:
        if chain[-1] in end_set:
            yield chain
        for nxt in FACES:
            if nxt not in chain and nxt[0] != chain[-1][0]:
                yield from extend(chain + (nxt,))

    for start in starts:
        yield from extend((start,))


def _initial_chart(face: Face) -> Chart:
    free = [i for i in range(3) if i != face[0]]
    columns: list[Vec2] = [(0.0, 0.0)] * 3
    columns[free[0]] = (1.0, 0.0)
    columns[free[1]] = (0.0, 1.0)
    return Chart(face, tuple(columns), (0.0, 0.0))  # type: ignore[arg-type]


def _shared_edge(sides: Vec3, face: Face, nxt: Face) -> tuple[Vec3, Vec3]:
    i, j = face[0], nxt[0]
    if i == j:
        raise ValueError("Equal or opposite faces do not share an edge")
    k = 3 - i - j
    lower = [0.0, 0.0, 0.0]
    lower[i], lower[j] = face[1] * sides[i], nxt[1] * sides[j]
    upper = lower.copy()
    upper[k] = sides[k]
    return tuple(lower), tuple(upper)  # type: ignore[return-value]


def develop_chain(sides: Vec3, chain: tuple[Face, ...]) -> tuple[Chart, ...]:
    """Place each new face on the other side of its shared developed edge."""
    charts = [_initial_chart(chain[0])]
    for face, nxt in zip(chain, chain[1:]):
        old = charts[-1]
        i, j = face[0], nxt[0]
        k = 3 - i - j
        # Positive signs indicate an inward increase of that coordinate.
        old_inward = 1.0 if nxt[1] == 0 else -1.0
        new_inward = 1.0 if face[1] == 0 else -1.0
        columns: list[Vec2] = [(0.0, 0.0)] * 3
        columns[i] = mul2(-old_inward * new_inward, old.columns[j])
        columns[k] = old.columns[k]
        anchor, _ = _shared_edge(sides, face, nxt)
        offset = sub2(old.project(anchor), mul2(anchor[i], columns[i]))
        charts.append(Chart(nxt, tuple(columns), offset))  # type: ignore[arg-type]
    return tuple(charts)


def _clip_unit_interval(lo: float, hi: float, tol: float) -> tuple[float, float] | None:
    lo, hi = max(0.0, lo), min(1.0, hi)
    if lo > hi + tol:
        return None
    if lo > hi:
        # Resolve a tolerance-sized discrepancy at an endpoint consistently.
        midpoint = min(1.0, max(0.0, (lo + hi) / 2.0))
        return midpoint, midpoint
    return lo, hi


def _line_edge_times(
    p: Vec2, q: Vec2, a: Vec2, b: Vec2, tol: float
) -> tuple[float, float] | None:
    """Parameters t where p+t(q-p) lies on the axis-aligned edge [a,b].

    The result can be an interval when the line runs along an edge.  Tiny
    nonzero direction components are not replaced by zero before division.
    """
    fixed = 0 if a[0] == b[0] else 1
    free = 1 - fixed
    if a[fixed] != b[fixed]:
        raise AssertionError("Developed box edges must be axis-aligned")
    direction = sub2(q, p)
    edge_lo, edge_hi = sorted((a[free], b[free]))
    if direction[fixed] != 0.0:
        t = (a[fixed] - p[fixed]) / direction[fixed]
        if t < -tol or t > 1.0 + tol:
            return None
        t = min(1.0, max(0.0, t))
        coordinate = p[free] + t * direction[free]
        if coordinate < edge_lo - tol or coordinate > edge_hi + tol:
            return None
        return t, t
    if abs(p[fixed] - a[fixed]) > tol:
        return None
    if direction[free] == 0.0:
        if edge_lo - tol <= p[free] <= edge_hi + tol:
            return 0.0, 1.0
        return None
    lo, hi = sorted(
        ((edge_lo - p[free]) / direction[free], (edge_hi - p[free]) / direction[free])
    )
    return _clip_unit_interval(lo, hi, tol)


def _in_face(chart: Chart, sides: Vec3, point: Vec2, tol: float) -> bool:
    coordinates = chart.lift(point, sides)
    return all(-tol <= value <= side + tol for value, side in zip(coordinates, sides))


def _valid_candidate(
    sides: Vec3, p: Vec3, q: Vec3, chain: tuple[Face, ...], tol: float
) -> _Candidate | None:
    charts = develop_chain(sides, chain)
    p2, q2 = charts[0].project(p), charts[-1].project(q)
    times: list[float] = []
    previous = 0.0
    for index, (face, nxt) in enumerate(zip(chain, chain[1:])):
        edge_a, edge_b = _shared_edge(sides, face, nxt)
        chart = charts[index]
        interval = _line_edge_times(p2, q2, chart.project(edge_a), chart.project(edge_b), tol)
        if interval is None:
            return None
        current = max(previous, interval[0])
        if current > interval[1] + tol:
            return None
        times.append(current)
        previous = current
    full_times = (0.0, *times, 1.0)
    # Each face is convex.  Its segment is inside precisely when both
    # endpoints are inside; no sampling of the face interior is needed.
    for chart, enter, leave in zip(charts, full_times, full_times[1:]):
        if not _in_face(chart, sides, lerp2(p2, q2, enter), 4 * tol):
            return None
        if not _in_face(chart, sides, lerp2(p2, q2, leave), 4 * tol):
            return None
    return _Candidate(math.dist(p2, q2), chain, charts, tuple(times), p2, q2)


def shortest_path(
    sides: Sequence[float], p: Sequence[float], q: Sequence[float], *, tol: float = 1e-10
) -> PathResult:
    """Compute a shortest surface path by checking every simple face chain.

    Tied chain counts include different descriptions of the same path at
    an edge or vertex; they are not counts of distinct geometric geodesics.
    """
    lengths, start, end, scale = _normalize_input(sides, p, q, tol)
    candidates: list[_Candidate] = []
    for chain in simple_face_chains(incident_faces(lengths, start), incident_faces(lengths, end)):
        candidate = _valid_candidate(lengths, start, end, chain, tol)
        if candidate is not None:
            candidates.append(candidate)
    if not candidates:
        raise ArithmeticError("No valid unfolding found; check inputs or numerical conditioning")
    best = min(candidates, key=lambda c: (c.distance, len(c.chain), c.chain))
    crossings = tuple(
        tuple(scale * value for value in best.charts[i].lift(lerp2(best.start2, best.end2, t), lengths))
        for i, t in enumerate(best.times)
    )
    return PathResult(
        distance=scale * best.distance,
        face_chain=tuple(face_name(face) for face in best.chain),
        crossing_points=crossings,  # type: ignore[arg-type]
        crossing_parameters=best.times,
        unfolded_start=mul2(scale, best.start2),
        unfolded_end=mul2(scale, best.end2),
        start=tuple(scale * x for x in start),  # type: ignore[arg-type]
        end=tuple(scale * x for x in end),  # type: ignore[arg-type]
        valid_chain_count=len(candidates),
        minimizing_chain_count=sum(abs(c.distance - best.distance) <= 8 * tol for c in candidates),
        tolerance_relative_to_largest_side=tol,
    )


def surface_distance(
    sides: Sequence[float], p: Sequence[float], q: Sequence[float], *, tol: float = 1e-10
) -> float:
    return shortest_path(sides, p, q, tol=tol).distance


def self_test() -> list[dict[str, object]]:
    """Small reproducible checks with independently known exact answers."""
    square_box_coordinate = (math.sqrt(3.0) - 1.0) / 2.0
    cases = [
        ("cube_opposite_vertices", (1, 1, 1), (0, 0, 0), (1, 1, 1), math.sqrt(5)),
        ("cube_face_diagonal", (1, 1, 1), (0, 0, 0), (1, 1, 0), math.sqrt(2)),
        ("coincident_corner", (1, 2, 3), (0, 0, 0), (0, 0, 0), 0.0),
        ("one_edge", (1, 2, 3), (0, 0, 0.4), (0, 0, 2.7), 2.3),
        ("same_face", (1, 2, 3), (0, 0.3, 0.8), (0, 1.7, 2.4), math.hypot(1.4, 1.6)),
        ("one_one_two_opposite_vertices", (1, 1, 2), (0, 0, 0), (1, 1, 2), math.sqrt(8)),
        ("one_one_two_vertex_farthest", (1, 1, 2), (0, 0, 0), (0.75, 0.75, 2), math.sqrt(65 / 8)),
        (
            "one_one_two_diameter", (1, 1, 2),
            (square_box_coordinate, square_box_coordinate, 0),
            (1 - square_box_coordinate, 1 - square_box_coordinate, 2),
            math.sqrt(16 - 4 * math.sqrt(3)),
        ),
        ("three_four_five_vertices", (3, 4, 5), (0, 0, 0), (3, 4, 5), math.sqrt(74)),
        ("spider_and_fly_five_faces", (30, 12, 12), (0, 6, 11), (30, 6, 1), 40.0),
    ]
    results: list[dict[str, object]] = []
    for name, sides, p, q, expected in cases:
        result = shortest_path(sides, p, q)
        if not math.isclose(result.distance, expected, rel_tol=2e-12, abs_tol=2e-12):
            raise AssertionError(f"{name}: got {result.distance}, expected {expected}")
        reverse = surface_distance(sides, q, p)
        if not math.isclose(reverse, result.distance, rel_tol=2e-12, abs_tol=2e-12):
            raise AssertionError(f"{name}: symmetry check failed")
        results.append({"name": name, "expected": expected, **asdict(result)})
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sides", nargs=3, type=float, metavar=("A", "B", "C"))
    parser.add_argument("--p", nargs=3, type=float, metavar=("X", "Y", "Z"))
    parser.add_argument("--q", nargs=3, type=float, metavar=("X", "Y", "Z"))
    parser.add_argument("--tol", type=float, default=1e-10)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps({"status": "passed", "tests": self_test()}, indent=2))
        return
    if args.sides is None or args.p is None or args.q is None:
        parser.error("provide --sides, --p, and --q, or use --self-test")
    print(json.dumps(asdict(shortest_path(args.sides, args.p, args.q, tol=args.tol)), indent=2))


if __name__ == "__main__":
    main()
