"""A deterministic O(s log s) terminal pattern test for a KNOWN 3-ball.

Here s is the number of darts; labels use O(log(s+2)) bits.  The topology of
the ambient manifold is a caller precondition, not established by this code.
Rotation triples specify spherical embeddings of cubic multigraph components;
vertex-free circle components are counted separately.  Relative nesting of
disconnected components cannot change the verdict, but is not reconstructed.

The algorithm validates the ribbon graph, constructs its embedded dual, rejects
dual loops and parallel edges, and uses a 5-degeneracy ordering to enumerate all
dual triangles.  A nonfacial triangle is the remaining obstruction.  Facial
triangles are stored with multiplicity: the two faces of K3 are not conflated.

No probabilistic hashing or generic vertex-connectivity algorithm is used in the
classifier.  A separate verifier checks negative witnesses as primal edge bonds.
"""
from __future__ import annotations

from bisect import bisect_left
from collections import deque
from dataclasses import dataclass
from itertools import combinations
from typing import Any, Mapping


class PatternError(ValueError):
    """Malformed input, or a rotation system that is not spherical."""


@dataclass(frozen=True)
class BallPattern:
    rotation: tuple[tuple[int, int, int], ...]
    circles: int = 0

    @classmethod
    def from_json(cls, data: Any) -> "BallPattern":
        return _parse(data).pattern

    def to_json(self) -> dict[str, Any]:
        return {"ambient": "3-ball", "rotation": [list(v) for v in self.rotation],
                "circles": self.circles}


@dataclass
class _Parsed:
    pattern: BallPattern
    sigma: list[int]
    dart_vertex: list[int]
    dart_face: list[int]
    faces: list[list[int]]
    vertex_component: list[int]
    components: list[list[int]]

    @property
    def edge_count(self) -> int:
        return len(self.sigma) // 2


def _parse(data: Any) -> _Parsed:
    if isinstance(data, BallPattern):
        data = data.to_json()
    if not isinstance(data, Mapping) or data.get("ambient") != "3-ball":
        raise PatternError("ambient must explicitly be '3-ball'")
    rows = data.get("rotation")
    if not isinstance(rows, (list, tuple)):
        raise PatternError("rotation must be a list of cyclic triples")
    circles = data.get("circles", 0)
    if type(circles) is not int or circles < 0:
        raise PatternError("circles must be a nonnegative integer")
    size = 3 * len(rows)
    if size % 2:
        raise PatternError("the number of darts must be even")
    sigma = [-1] * size
    dart_vertex = [-1] * size
    rotation = []
    for vertex, row in enumerate(rows):
        if not isinstance(row, (list, tuple)) or len(row) != 3:
            raise PatternError("each graph vertex must have degree three")
        for d in row:
            if type(d) is not int or not 0 <= d < size:
                raise PatternError("darts must be integers from 0 through 2E-1")
            if dart_vertex[d] != -1:
                raise PatternError("every dart must occur exactly once")
            dart_vertex[d] = vertex
        a, b, c = row
        sigma[a], sigma[b], sigma[c] = b, c, a
        rotation.append((a, b, c))
    # Exactly 'size' distinct entries in [0, size) have now been read.
    owner = [-1] * len(rotation)
    components = []
    for root in range(len(rotation)):
        if owner[root] != -1:
            continue
        component_id = len(components)
        owner[root] = component_id
        stack, part = [root], []
        while stack:
            v = stack.pop()
            part.append(v)
            for d in rotation[v]:
                u = dart_vertex[d ^ 1]
                if owner[u] == -1:
                    owner[u] = component_id
                    stack.append(u)
        components.append(part)
    dart_face = [-1] * size
    faces = []
    for first in range(size):
        if dart_face[first] != -1:
            continue
        face_id = len(faces)
        face, d = [], first
        while dart_face[d] == -1:
            dart_face[d] = face_id
            face.append(d)
            d = sigma[d ^ 1]
        faces.append(face)
    edges_per_part = [0] * len(components)
    faces_per_part = [0] * len(components)
    for d in range(0, size, 2):
        edges_per_part[owner[dart_vertex[d]]] += 1
    for face in faces:
        faces_per_part[owner[dart_vertex[face[0]]]] += 1
    for i, part in enumerate(components):
        if len(part) - edges_per_part[i] + faces_per_part[i] != 2:
            raise PatternError("every graph rotation component must be spherical")
    return _Parsed(BallPattern(tuple(rotation), circles), sigma, dart_vertex,
                   dart_face, faces, owner, components)


def _cut_sides(p: _Parsed, cut: tuple[int, ...]) -> list[list[int]]:
    """Primal components after removing at most three specified edges."""
    seen = [False] * len(p.pattern.rotation)
    sides = []
    for root in range(len(seen)):
        if seen[root]:
            continue
        seen[root] = True
        stack, part = [root], []
        while stack:
            v = stack.pop()
            part.append(v)
            for d in p.pattern.rotation[v]:
                if d // 2 in cut:
                    continue
                u = p.dart_vertex[d ^ 1]
                if not seen[u]:
                    seen[u] = True
                    stack.append(u)
        # Produce canonical vertex lists without set/dictionary operations.
        part.sort()
        sides.append(part)
    return sides


def _cycle_witness(p: _Parsed, vertices: tuple[int, ...],
                   edges: tuple[int, ...]) -> dict[str, Any]:
    size = len(edges)
    sides = _cut_sides(p, edges)
    if len(sides) != 2 or (size == 3 and min(map(len, sides)) <= 1):
        raise RuntimeError("internal error: a proposed dual cycle is not violating")
    kinds = {1: "dual-loop", 2: "dual-bigon", 3: "nonfacial-dual-triangle"}
    return {"kind": kinds[size], "intersections": size,
            "dual_vertices": list(vertices), "primal_edges": list(edges),
            "vertex_sides": sides}


def _face_pairs(p: _Parsed) -> list[tuple[int, int, int]]:
    edges = []
    for e in range(p.edge_count):
        a, b = p.dart_face[2 * e], p.dart_face[2 * e + 1]
        if a > b:
            a, b = b, a
        edges.append((a, b, e))
    return sorted(edges)


def classify_pattern(data: Any) -> dict[str, Any]:
    """Validate raw input and return essentiality with a checked obstruction.

    Runtime is O(s log(s+2)) deterministic RAM operations, and space is O(s).
    The binary length of a separately supplied circle count is also input cost.
    """
    p = _parse(data)
    count = len(p.components) + p.pattern.circles
    result: dict[str, Any] = {
        "schema": "ball-pattern-result-v2",
        "input": p.pattern.to_json(),
        "algorithm": "dual-triangles-via-five-degeneracy",
        "worst_case": "O(s log(s+2)) deterministic RAM operations",
        "precondition": "ambient is a known 3-ball",
        "darts": len(p.sigma),
    }
    if count > 1:
        result.update(status="violating", witness={
            "kind": "disconnected-pattern", "intersections": 0,
            "graph_components": len(p.components), "circles": p.pattern.circles,
            "component_count": count,
        })
        return result
    if count == 0 or p.pattern.circles == 1:
        result.update(status="essential", candidate_pairs=0,
                      dual_triangles=0, facial_triangles=0,
                      distinct_facial_triangles=0, max_forward_degree=0)
        return result

    edges = _face_pairs(p)
    for a, b, e in edges:
        if a == b:
            result.update(status="violating",
                          witness=_cycle_witness(p, (a,), (e,)))
            return result
    for left, right in zip(edges, edges[1:]):
        a, b, e = left
        c, d, f = right
        if (a, b) == (c, d):
            result.update(status="violating",
                          witness=_cycle_witness(p, (a, b), (e, f)))
            return result

    # The dual is now a simple planar graph.  Each primal vertex is one
    # triangular dual face; retain both occurrences when the dual is K3.
    facial = sorted(tuple(sorted(p.dart_face[d] for d in row))
                    for row in p.pattern.rotation)
    if any(not face[0] < face[1] < face[2] for face in facial):
        raise RuntimeError("internal error: simple dual has a nontriangular face")
    distinct_facials = sum(i == 0 or facial[i] != facial[i - 1]
                          for i in range(len(facial)))
    n = len(p.faces)
    adjacency: list[list[int]] = [[] for _ in range(n)]
    edge_keys = []
    edge_ids = []
    for a, b, e in edges:
        adjacency[a].append(b)
        adjacency[b].append(a)
        edge_keys.append((a, b))
        edge_ids.append(e)

    # Every nonempty subgraph of a simple planar graph has a vertex of
    # degree at most five.  A vertex is queued once, initially or on its
    # first transition from degree six to degree five.
    degree = list(map(len, adjacency))
    queue = deque(v for v in range(n) if degree[v] <= 5)
    removed = [False] * n
    forward: list[list[int]] = [[] for _ in range(n)]
    deleted = 0
    for_count = 0
    while queue:
        v = queue.popleft()
        if removed[v]:
            continue
        live = [u for u in adjacency[v] if not removed[u]]
        if len(live) > 5:
            raise RuntimeError("internal error: invalid planar degeneracy order")
        forward[v] = live
        for_count = max(for_count, len(live))
        removed[v] = True
        deleted += 1
        for u in live:
            degree[u] -= 1
            if degree[u] == 5:
                queue.append(u)
    if deleted != n:
        raise RuntimeError("internal error: planar degeneracy order did not finish")

    def edge_index(a: int, b: int) -> int:
        key = (a, b) if a < b else (b, a)
        i = bisect_left(edge_keys, key)
        return i if i < len(edge_keys) and edge_keys[i] == key else -1

    candidate_pairs = 0
    triangles = 0
    for u, outgoing in enumerate(forward):
        for v, w in combinations(outgoing, 2):
            candidate_pairs += 1
            vw = edge_index(v, w)
            if vw < 0:
                continue
            triangles += 1
            key = tuple(sorted((u, v, w)))
            i = bisect_left(facial, key)
            if i < len(facial) and facial[i] == key:
                continue
            uv, wu = edge_index(u, v), edge_index(w, u)
            witness = _cycle_witness(
                p, (u, v, w), (edge_ids[uv], edge_ids[vw], edge_ids[wu]))
            result.update(status="violating", witness=witness,
                          candidate_pairs=candidate_pairs, dual_triangles=triangles,
                          facial_triangles=len(facial),
                          distinct_facial_triangles=distinct_facials,
                          max_forward_degree=for_count)
            return result
    result.update(status="essential", candidate_pairs=candidate_pairs,
                  dual_triangles=triangles, facial_triangles=len(facial),
                  distinct_facial_triangles=distinct_facials,
                  max_forward_degree=for_count)
    return result


def verify_violating_witness(data: Any, witness: Any) -> bool:
    """Check a negative certificate via primal connectivity, not triangle search.

    Invalid pattern inputs raise PatternError.  Malformed or false witnesses
    return False.  The ambient 3-ball precondition remains the caller's duty.
    """
    p = _parse(data)
    if not isinstance(witness, Mapping):
        return False
    if type(witness.get("intersections")) is not int:
        return False
    count = len(p.components) + p.pattern.circles
    if witness.get("kind") == "disconnected-pattern":
        return (count > 1 and witness.get("intersections") == 0
                and witness.get("component_count") == count
                and witness.get("graph_components") == len(p.components)
                and witness.get("circles") == p.pattern.circles)
    kind_size = {"dual-loop": 1, "dual-bigon": 2,
                 "nonfacial-dual-triangle": 3}
    kind = witness.get("kind")
    if not isinstance(kind, str):
        return False
    size = kind_size.get(kind)
    if size is None or count != 1 or p.pattern.circles:
        return False
    vertices, edges = witness.get("dual_vertices"), witness.get("primal_edges")
    if (not isinstance(vertices, list) or not isinstance(edges, list)
            or len(vertices) != size or len(edges) != size
            or witness.get("intersections") != size):
        return False
    if any(type(v) is not int or not 0 <= v < len(p.faces) for v in vertices):
        return False
    if any(type(e) is not int or not 0 <= e < p.edge_count for e in edges):
        return False
    if len(set(vertices)) != size or len(set(edges)) != size:
        return False
    for i, e in enumerate(edges):
        a, b = p.dart_face[2 * e], p.dart_face[2 * e + 1]
        c, d = vertices[i], vertices[(i + 1) % size]
        if (a, b) != (c, d) and (a, b) != (d, c):
            return False
    sides = _cut_sides(p, tuple(edges))
    supplied_sides = witness.get("vertex_sides")
    if (not isinstance(supplied_sides, list)
            or any(not isinstance(side, list)
                   or any(type(v) is not int for v in side)
                   for side in supplied_sides)):
        return False
    if len(sides) != 2 or supplied_sides != sides:
        return False
    first = [False] * len(p.pattern.rotation)
    for v in sides[0]:
        first[v] = True
    boundary = []
    for e in range(p.edge_count):
        a, b = p.dart_vertex[2 * e], p.dart_vertex[2 * e + 1]
        if first[a] != first[b]:
            boundary.append(e)
    if boundary != sorted(edges):
        return False
    return size != 3 or min(map(len, sides)) > 1


def main() -> None:
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    args = parser.parse_args()
    result = classify_pattern(json.loads(args.input.read_text()))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
