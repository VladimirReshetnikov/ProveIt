#!/usr/bin/env python3
"""Exact finite kernel accompanying the constructive Jordan proof.

This is an executable reference implementation, NOT a formal proof of the
general continuous-curve theorem.  All geometry is rational and exact.  The
demonstrations take a polygon as a finite distance oracle; the article explains
how certified finite samples replace it for a general presented Jordan curve.

No operation below searches without an a priori finite bound.  Python's gcd,
dictionaries, and Fraction normalization are convenient representations, not
claims about a particular small complexity class.  Their elementary bounded
implementations are primitive recursive.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Callable, Iterable

Point = tuple[Q, Q]
Cell = tuple[int, int]
Edge = tuple[Point, Point]


def point(x: int | str | Q, y: int | str | Q) -> Point:
    return Q(x), Q(y)


def add(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def sub(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def mul(t: Q, a: Point) -> Point:
    return t * a[0], t * a[1]


def dot(a: Point, b: Point) -> Q:
    return a[0] * b[0] + a[1] * b[1]


def cross(a: Point, b: Point) -> Q:
    return a[0] * b[1] - a[1] * b[0]


def orient(a: Point, b: Point, p: Point) -> Q:
    return cross(sub(b, a), sub(p, a))


def norm_sq(a: Point) -> Q:
    return dot(a, a)


def linf(a: Point) -> Q:
    return max(abs(a[0]), abs(a[1]))


def on_segment(p: Point, a: Point, b: Point) -> bool:
    return orient(a, b, p) == 0 and dot(sub(p, a), sub(p, b)) <= 0


def segments_meet(a: Point, b: Point, c: Point, d: Point) -> bool:
    ab_c, ab_d = orient(a, b, c), orient(a, b, d)
    cd_a, cd_b = orient(c, d, a), orient(c, d, b)
    if ((ab_c > 0 and ab_d < 0) or (ab_c < 0 and ab_d > 0)) and (
        (cd_a > 0 and cd_b < 0) or (cd_a < 0 and cd_b > 0)
    ):
        return True
    return any((on_segment(c, a, b), on_segment(d, a, b),
                on_segment(a, c, d), on_segment(b, c, d)))


def point_segment_distance_sq(p: Point, a: Point, b: Point) -> Q:
    v, w = sub(b, a), sub(p, a)
    vv = norm_sq(v)
    if vv == 0:
        return norm_sq(w)
    t = dot(w, v)
    if t <= 0:
        return norm_sq(w)
    if t >= vv:
        return norm_sq(sub(p, b))
    return norm_sq(w) - t * t / vv


def segment_distance_sq(a: Point, b: Point, c: Point, d: Point) -> Q:
    if segments_meet(a, b, c, d):
        return Q(0)
    return min(point_segment_distance_sq(a, c, d),
               point_segment_distance_sq(b, c, d),
               point_segment_distance_sq(c, a, b),
               point_segment_distance_sq(d, a, b))


def point_segment_distance_linf(p: Point, a: Point, b: Point) -> Q:
    """Exact minimum of four affine functions' maximum on [0,1]."""
    w, v = sub(a,p), sub(b,a)
    affine = [(w[0],v[0]),(-w[0],-v[0]),(w[1],v[1]),(-w[1],-v[1])]
    candidates = [Q(0),Q(1)]
    for i in range(4):
        for j in range(i+1,4):
            c1,m1 = affine[i]
            c2,m2 = affine[j]
            if m1 != m2:
                t = (c2-c1)/(m1-m2)
                if 0 <= t <= 1:
                    candidates.append(t)
    return min(linf(add(w,mul(t,v))) for t in candidates)


def segment_distance_linf(a: Point, b: Point, c: Point, d: Point) -> Q:
    """Use the boundary of the convex Minkowski difference [a,b]-[c,d]."""
    if segments_meet(a,b,c,d):
        return Q(0)
    return min(point_segment_distance_linf(a,c,d),
               point_segment_distance_linf(b,c,d),
               point_segment_distance_linf(c,a,b),
               point_segment_distance_linf(d,a,b))


def closed_edges(vertices: Iterable[Point]) -> list[Edge]:
    v = list(vertices)
    if not v:
        return []
    return list(zip(v, v[1:] + v[:1]))


def segment_polygon_clearance_sq(a: Point, b: Point,
                                 polygon: list[Point]) -> Q:
    if not polygon:
        raise ValueError("The distance oracle needs a nonempty polygon")
    return min(segment_distance_sq(a, b, c, d)
               for c, d in closed_edges(polygon))


def segment_polygon_clearance_linf(a: Point, b: Point,
                                   polygon: list[Point]) -> Q:
    if not polygon:
        raise ValueError("The distance oracle needs a nonempty polygon")
    return min(segment_distance_linf(a,b,c,d) for c,d in closed_edges(polygon))


def point_polygon_clearance_sq(p: Point, polygon: list[Point]) -> Q:
    return segment_polygon_clearance_sq(p, p, polygon)


def path_polygon_clearance_sq(path: list[Point], polygon: list[Point]) -> Q:
    if not path:
        raise ValueError("A path must have an endpoint")
    if len(path) == 1:
        return point_polygon_clearance_sq(path[0], polygon)
    return min(segment_polygon_clearance_sq(a, b, polygon)
               for a, b in zip(path, path[1:]))


def path_polygon_clearance_linf(path: list[Point], polygon: list[Point]) -> Q:
    if not path:
        raise ValueError("A path must have an endpoint")
    pairs = list(zip(path,path[1:])) or [(path[0],path[0])]
    return min(segment_polygon_clearance_linf(a,b,polygon) for a,b in pairs)


def edge_index(a: Point, b: Point, p: Point) -> int:
    """Signed crossing of the positive horizontal ray at p.

    The y intervals are half open.  Thus vertices on the ray are counted
    consistently, including horizontal edges.  p itself must be off [a,b].
    """
    if on_segment(p, a, b):
        raise ValueError("Index requires a point off the polygon")
    d = orient(a, b, p)
    if a[1] <= p[1] < b[1] and d > 0:
        return 1
    if b[1] <= p[1] < a[1] and d < 0:
        return -1
    return 0


def winding(polygon: list[Point], p: Point) -> int:
    """Integer index; self-intersections and repeated traversals are allowed."""
    return sum(edge_index(a, b, p) for a, b in closed_edges(polygon))


def crossing_parity(polygon: list[Point], p: Point) -> int:
    """The 0/1 index used by the main proof; orientation is immaterial."""
    return winding(polygon, p) % 2


def polygon_simple(polygon: list[Point]) -> bool:
    """Exact decidable simplicity predicate for a finite rational polygon."""
    n = len(polygon)
    if n < 3 or len(set(polygon)) != n:
        return False
    edges = closed_edges(polygon)
    for i in range(n):
        a, b = edges[i]
        if a == b:
            return False
        for j in range(i + 1, n):
            c, d = edges[j]
            if j == i + 1 or (i == 0 and j == n - 1):
                common = b if j == i + 1 else a
                other1 = a if common == b else b
                other2 = d if common == c else c
                if on_segment(other1, common, other2) or on_segment(other2, common, other1):
                    return False
            elif segments_meet(a, b, c, d):
                return False
    return True


HEX_OFFSETS = ((2, 0), (1, 1), (-1, 1), (-2, 0), (-1, -1), (1, -1))
# Neighbor k lies across the k-th counterclockwise edge.
NEIGHBOR_OFFSETS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def center(cell: Cell, h: Q = Q(1), origin: Point = point(0, 0)) -> Point:
    i, j = cell
    return add(origin, point(3 * i * h, (i + 2 * j) * h))


def hexagon(cell: Cell, h: Q = Q(1), origin: Point = point(0, 0)) -> list[Point]:
    c = center(cell, h, origin)
    return [add(c, point(x * h, y * h)) for x, y in HEX_OFFSETS]


def neighbor(cell: Cell, k: int) -> Cell:
    di, dj = NEIGHBOR_OFFSETS[k]
    return cell[0] + di, cell[1] + dj


def patch(radius: int) -> list[Cell]:
    if radius < 1:
        raise ValueError("A patch needs a positive radius")
    return [(i, j) for i in range(-radius, radius + 1)
            for j in range(-radius, radius + 1)]


@dataclass
class Flood:
    cells: list[Cell]
    root: Cell
    parent: dict[Cell, Cell | None]
    green_links: dict[tuple[Cell, Cell], bool]
    evaluations: int

    def reached(self, cell: Cell) -> bool:
        return cell in self.parent

    def path_to(self, goal: Cell) -> list[Cell]:
        if goal not in self.parent:
            raise ValueError("Goal is not in the reached component")
        rev = [goal]
        current = goal
        for _ in range(len(self.cells)):
            prev = self.parent[current]
            if prev is None:
                return list(reversed(rev))
            rev.append(prev)
            current = prev
        raise AssertionError("Parent chain exceeded the number of cells")


def flood(cells: list[Cell], root: Cell,
          link_is_green: Callable[[Cell, Cell], bool]) -> Flood:
    """Finite BFS with at most V vertex steps and at most 6V link tests."""
    allowed = set(cells)
    if len(allowed) != len(cells) or root not in allowed:
        raise ValueError("Distinct cells and a root in the patch are required")
    parents: dict[Cell, Cell | None] = {root: None}
    queue = [root]
    links: dict[tuple[Cell, Cell], bool] = {}
    evaluations = 0
    for step in range(len(cells)):
        if step >= len(queue):
            break
        c = queue[step]
        for k in range(6):
            d = neighbor(c, k)
            if d not in allowed:
                continue
            key = tuple(sorted((c, d)))
            if key not in links:
                links[key] = bool(link_is_green(c, d))
                evaluations += 1
            if links[key] and d not in parents:
                parents[d] = c
                queue.append(d)
    assert len(queue) <= len(cells)
    assert evaluations <= 6 * len(cells)
    return Flood(cells, root, parents, links, evaluations)


def boundary_cycles(cells: list[Cell], green: set[Cell], h: Q = Q(1),
                    origin: Point = point(0, 0)) -> list[list[Point]]:
    """Extract internal separating cycles, with green on their left.

    The intended precondition is a uniformly colored outer collar.  The
    function checks the exact consequence it uses: every boundary vertex has
    one incoming and one outgoing edge.  It never assumes a Jordan theorem.
    """
    allowed = set(cells)
    if not green <= allowed:
        raise ValueError("Colors were given outside the patch")
    edges: set[Edge] = set()
    for c in cells:
        if c not in green:
            continue
        vv = hexagon(c, h, origin)
        for k in range(6):
            d = neighbor(c, k)
            if d in allowed and d not in green:
                edges.add((vv[k], vv[(k + 1) % 6]))
    nxt: dict[Point, Point] = {}
    prev: dict[Point, Point] = {}
    for a, b in edges:
        if a in nxt or b in prev:
            raise ValueError("Boundary is not a directed degree-two graph")
        nxt[a], prev[b] = b, a
    if set(nxt) != set(prev):
        raise ValueError("Boundary reaches the edge of the patch")
    used: set[Point] = set()
    loops: list[list[Point]] = []
    for root in sorted(nxt):
        if root in used:
            continue
        path: list[Point] = []
        v = root
        closed = False
        for _ in range(len(edges) + 1):
            if path and v == root:
                closed = True
                break
            if v in used:
                raise AssertionError("A directed orbit merged before closing")
            used.add(v)
            path.append(v)
            v = nxt[v]
        if not closed or len(path) < 3:
            raise AssertionError("Finite degree-two orbit did not form a cycle")
        if not polygon_simple(path):
            raise AssertionError("Honeycomb boundary cycle is not geometrically simple")
        loops.append(path)
    assert len(used) == len(edges)
    return loops


def polygon_flood(polygon: list[Point], radius: int, root: Cell,
                  h: Q = Q(1), origin: Point = point(0, 0)) -> Flood:
    """Use an exact polygon distance oracle and l-infinity clearance at least h."""
    if h <= 0:
        raise ValueError("Scale must be positive")
    return flood(patch(radius), root,
                 lambda c, d: segment_polygon_clearance_linf(
                     center(c, h, origin), center(d, h, origin), polygon) >= h)


def sample_polygon(polygon: list[Point], subdivisions: int) -> list[Point]:
    if subdivisions < 1:
        raise ValueError("Positive subdivision count required")
    return [add(a, mul(Q(k, subdivisions), sub(b, a)))
            for a, b in closed_edges(polygon) for k in range(subdivisions)]


def nearest_labels(vertices: list[Point], samples: list[Point]) -> list[int]:
    """Bounded nearest-sample labeling, with lexicographic tie breaking."""
    if not samples:
        raise ValueError("Nonempty sample needed")
    return [min(range(len(samples)), key=lambda k: (linf(sub(x, samples[k])), k))
            for x in vertices]


def circle_walk_degree(labels: list[int], sample_count: int) -> int:
    """Degree of the concatenated shorter cyclic walks between labels.

    A tie at exactly half a circle is rejected; the proof's separation modulus
    guarantees much shorter jumps.  Cancellation is exact integer arithmetic.
    """
    if sample_count < 3 or not labels:
        raise ValueError("At least three cyclic samples and one label required")
    if any(k < 0 or k >= sample_count for k in labels):
        raise ValueError("Invalid cyclic label")
    total = 0
    for a, b in zip(labels, labels[1:] + labels[:1]):
        delta = (b - a) % sample_count
        if 2 * delta == sample_count:
            raise ValueError("Antipodal cyclic labels")
        if 2 * delta > sample_count:
            delta -= sample_count
        total += delta
    if total % sample_count:
        raise AssertionError("Closed cyclic walk did not have integral degree")
    return total // sample_count


def json_point(p: Point) -> list[str]:
    return [str(p[0]), str(p[1])]


def json_path(path: list[Point]) -> list[list[str]]:
    return [json_point(p) for p in path]
