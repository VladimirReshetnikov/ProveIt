"""Native compressed topology and certificates for a supplied normal surface.

The tetrahedral matching and polygon extraction come from the previous affine
families report.  General interval orbit reduction is now supplied by the
Agol--Hass--Thurston engine.  No normal disc or sheet is expanded.

The input face pairings must describe a compact triangulated 3-manifold.  We
check the combinatorial schema, matching equations, quadrilateral constraints,
and consistency of edge orientations and intersection counts.  Vertex links,
irreducibility, and provenance as an S^3 knot exterior remain preconditions.
The result certifies properties of a *supplied* normal vector; it does not
search for that vector or independently recognize the ambient manifold.
"""

from __future__ import annotations

from collections import deque
from hashlib import sha256
from itertools import combinations
import json

from .interval_orbits import analyze_orbits
from .integer_codec import encoded_integer
from .normal_interval_extraction import (
    ExtractionError, encode_large_integers, extract_normal_intervals, orbit_input,
)


_EDGES = tuple(combinations(range(4), 2))
_EDGE_INDEX = {edge: index for index, edge in enumerate(_EDGES)}


class _SignedDSU:
    """A finite, tetrahedron-sized DSU; never indexed by normal multiplicity."""

    def __init__(self, size):
        self.parent = list(range(size))
        self.rank = [0] * size
        self.flip = [0] * size

    def find(self, item):
        if self.parent[item] != item:
            parent, parity = self.find(self.parent[item])
            self.flip[item] ^= parity
            self.parent[item] = parent
        return self.parent[item], self.flip[item]

    def join(self, left, right, parity=0):
        a, x = self.find(left)
        b, y = self.find(right)
        if a == b:
            if x ^ y != parity:
                raise ExtractionError("a tetrahedral edge is identified with its reversal")
            return
        if self.rank[a] < self.rank[b]:
            a, b = b, a
        self.parent[b] = a
        self.flip[b] = x ^ y ^ parity
        if self.rank[a] == self.rank[b]:
            self.rank[a] += 1


def _poll(check):
    if check is not None:
        check()


def cone_pairings(size, pairings, intervals, *, check=None):
    """Join every original orbit meeting the specified union into one orbit.

Returns (new_pairings, nonempty).  For a nonempty marked union the number of
original touched orbits is C_original - C_new + 1.  Intervals are half-open.
This uses O(number of intervals) partial isometries, regardless of their width.
"""
    merged = []
    for lo, hi in sorted(intervals):
        _poll(check)
        if type(lo) is not int or type(hi) is not int or not 0 <= lo <= hi <= size:
            raise ValueError("marked interval outside the universe")
        if lo == hi:
            continue
        if merged and lo <= merged[-1][1]:
            merged[-1][1] = max(hi, merged[-1][1])
        else:
            merged.append([lo, hi])
    output = list(pairings)
    if not merged:
        return output, False
    hub = merged[0][0]
    for lo, hi in merged:
        _poll(check)
        if hi - lo > 1:
            output.append({"start": lo, "stop": hi - 1, "sign": 1, "offset": 1})
        if lo != hub:
            output.append({"start": hub, "stop": hub + 1,
                           "sign": 1, "offset": lo - hub})
    return output, True


def _ambient_edges(raw, result, check):
    """Finite edge/vertex classes, exact normal vertex counts and boundary graph."""
    t = result.tetrahedra
    vertices, edges = _SignedDSU(4 * t), _SignedDSU(6 * t)
    for tet, faces in enumerate(raw["tetrahedra"]):
        for face, rec in enumerate(faces):
            _poll(check)
            if rec is None:
                continue
            target, permutation = rec["tetrahedron"], rec["permutation"]
            if (tet, face) > (target, permutation[face]):
                continue
            for vertex in range(4):
                if vertex != face:
                    vertices.join(4 * tet + vertex, 4 * target + permutation[vertex])
            for edge in _EDGES:
                if face in edge:
                    continue
                image = (permutation[edge[0]], permutation[edge[1]])
                edges.join(6 * tet + _EDGE_INDEX[edge],
                           6 * target + _EDGE_INDEX[tuple(sorted(image))],
                           int(image[0] > image[1]))
    intersection = [0] * (6 * t)
    for stack in result.stacks:
        _poll(check)
        for edge in stack.corners:
            intersection[6 * stack.tetrahedron + _EDGE_INDEX[edge]] += stack.count
    counts, representatives = {}, {}
    for local, count in enumerate(intersection):
        _poll(check)
        root, _ = edges.find(local)
        if root in counts and count != counts[root]:
            raise ExtractionError("normal intersection counts disagree around an edge")
        counts[root] = count
        representatives[root] = min(local, representatives.get(root, local))
    boundary = set()
    for tet, faces in enumerate(raw["tetrahedra"]):
        for face, rec in enumerate(faces):
            _poll(check)
            if rec is None:
                for edge in _EDGES:
                    if face not in edge:
                        boundary.add(edges.find(6 * tet + _EDGE_INDEX[edge])[0])
    graph = []
    for root in sorted(boundary, key=representatives.get):
        _poll(check)
        local = representatives[root]
        tet, e = divmod(local, 6)
        a, b = _EDGES[e]
        graph.append((vertices.find(4 * tet + a)[0],
                      vertices.find(4 * tet + b)[0], counts[root] & 1))
    return edges, boundary, sum(counts.values()), graph


def _parity_certificate(graph, check):
    """Prove a boundary cocycle exact by vertex values, or nonexact by a cycle."""
    adjacency = {}
    for index, (a, b, parity) in enumerate(graph):
        adjacency.setdefault(a, []).append((b, parity, index))
        adjacency.setdefault(b, []).append((a, parity, index))
    values, parent = {}, {}
    for root in sorted(adjacency):
        _poll(check)
        if root in values:
            continue
        values[root] = 0
        parent[root] = None
        pending = deque([root])
        while pending:
            _poll(check)
            current = pending.popleft()
            for other, parity, index in adjacency[current]:
                expected = values[current] ^ parity
                if other not in values:
                    values[other] = expected
                    parent[other] = (current, index)
                    pending.append(other)
                elif values[other] != expected:
                    cycle = {index}
                    for start in (current, other):
                        while parent[start] is not None:
                            _poll(check)
                            previous, edge = parent[start]
                            cycle.symmetric_difference_update((edge,))
                            start = previous
                    return {"nonzero": True, "cycle_edges": sorted(cycle)}
    return {"nonzero": False, "vertex_values": [[key, values[key]] for key in sorted(values)]}


def _verify_parity(graph, proof, check):
    if type(proof) is not dict or type(proof.get("nonzero")) is not bool:
        return False
    if proof["nonzero"]:
        if set(proof) != {"nonzero", "cycle_edges"}:
            return False
        chosen = proof["cycle_edges"]
        if (type(chosen) is not list or not chosen or
                any(type(i) is not int or not 0 <= i < len(graph) for i in chosen) or
                len(set(chosen)) != len(chosen)):
            return False
        odd, parity = set(), 0
        for index in chosen:
            _poll(check)
            a, b, bit = graph[index]
            odd.symmetric_difference_update((a,))
            odd.symmetric_difference_update((b,))
            parity ^= bit
        return not odd and parity == 1
    if set(proof) != {"nonzero", "vertex_values"}:
        return False
    values = proof["vertex_values"]
    if type(values) is not list:
        return False
    assigned = {}
    for pair in values:
        if (type(pair) is not list or len(pair) != 2 or
                type(pair[0]) is not int or type(pair[1]) is not int or
                pair[1] not in (0, 1) or pair[0] in assigned):
            return False
        assigned[pair[0]] = pair[1]
    if set(assigned) != {v for a, b, _ in graph for v in (a, b)}:
        return False
    return all(assigned[a] ^ assigned[b] == parity for a, b, parity in graph)


def _queries(triangulation, coordinates, check):
    result = extract_normal_intervals(triangulation, coordinates,
                                     check=lambda: _poll(check))
    edges, boundary_edges, vertices, graph = _ambient_edges(triangulation, result, check)
    ordinary = orbit_input(result, check=lambda: _poll(check))
    oriented = orbit_input(result, orientation_cover=True, check=lambda: _poll(check))
    size = ordinary["universe_stop"]
    offsets, position = [], 0
    for stack in result.stacks:
        offsets.append(position)
        position += stack.count
    marked = [(offsets[b.stack], offsets[b.stack] + b.count) for b in result.boundary_bands]
    cone, nonempty = cone_pairings(size, ordinary["pairings"], marked, check=check)
    lifted_marks = marked + [(a + size, b + size) for a, b in marked]
    lifted_cone, _ = cone_pairings(2 * size, oriented["pairings"], lifted_marks, check=check)
    queries = {
        "components": (size, ordinary["pairings"]),
        "orientation_components": (2 * size, oriented["pairings"]),
    }
    if nonempty:
        queries["boundary_component_cone"] = size, cone
        queries["boundary_orientation_cone"] = 2 * size, lifted_cone

    # Retain only corners on ambient boundary edges. Glued sides identify the
    # local copies of vertices; boundary sides join consecutive boundary vertices.
    corner_offsets, corner_size = {}, 0
    for stack in result.stacks:
        for corner, edge in enumerate(stack.corners):
            _poll(check)
            if edges.find(6 * stack.tetrahedron + _EDGE_INDEX[edge])[0] in boundary_edges:
                corner_offsets[stack.identifier, corner] = corner_size
                corner_size += stack.count
    boundary_pairings = []
    for band in result.surface_bands:
        _poll(check)
        source, target = result.stacks[band.source_stack], result.stacks[band.target_stack]
        side = source.side_faces.index(band.source_face)
        for corner in (side, (side + 1) % len(source.corners)):
            key = source.identifier, corner
            if key not in corner_offsets:
                continue
            mapped = tuple(sorted(band.permutation[v] for v in source.corners[corner]))
            other = target.identifier, target.corners.index(mapped)
            src, dst = corner_offsets[key], corner_offsets[other]
            boundary_pairings.append({"start": src + band.start, "stop": src + band.stop,
                                      "sign": band.sign,
                                      "offset": dst + band.offset - band.sign * src})
    for band in result.boundary_bands:
        _poll(check)
        stack = result.stacks[band.stack]
        side = stack.side_faces.index(band.face)
        src = corner_offsets[stack.identifier, side]
        dst = corner_offsets[stack.identifier, (side + 1) % len(stack.corners)]
        boundary_pairings.append({"start": src, "stop": src + band.count,
                                  "sign": 1, "offset": dst - src})
    queries["boundary_cycles"] = corner_size, boundary_pairings
    sides = sum(len(s.corners) * s.count for s in result.stacks)
    boundary_arcs = sum(b.count for b in result.boundary_bands)
    if (sides + boundary_arcs) & 1:
        raise ExtractionError("the polygon-side parity is inconsistent")
    edges_count = (sides + boundary_arcs) // 2
    facts = {"normal_discs": size, "vertices": vertices, "edges": edges_count,
             "boundary_arcs": boundary_arcs,
             "euler_characteristic": vertices - edges_count + size,
             "has_boundary": nonempty}
    return result, queries, facts, graph


def _summary(counts, facts, nonzero):
    total, lifted = counts["components"], counts["orientation_components"]
    touched = total - counts["boundary_component_cone"] + 1 if facts["has_boundary"] else 0
    lifted_touched = (lifted - counts["boundary_orientation_cone"] + 1
                      if facts["has_boundary"] else 0)
    orientable, nonorientable = lifted - total, 2 * total - lifted
    boundary_orientable = lifted_touched - touched
    boundary_nonorientable = 2 * touched - lifted_touched
    is_disk = total == 1 and orientable == 1 and facts["euler_characteristic"] == 1
    return {**facts, "components": total, "orientable_components": orientable,
            "nonorientable_components": nonorientable,
            "components_with_boundary": touched,
            "closed_components": total - touched,
            "orientable_components_with_boundary": boundary_orientable,
            "nonorientable_components_with_boundary": boundary_nonorientable,
            "closed_orientable_components": orientable - boundary_orientable,
            "closed_nonorientable_components": nonorientable - boundary_nonorientable,
            "boundary_components": counts["boundary_cycles"],
            "boundary_homology_nonzero_mod2": nonzero,
            "is_disk": is_disk, "certifies_compressing_disk": is_disk and nonzero}


def _fingerprint(triangulation, coordinates):
    # Hex transport avoids Python's decimal conversion ceiling at arbitrary B.
    body = json.dumps(encode_large_integers({"triangulation": triangulation,
                                            "coordinates": coordinates}, threshold_bits=0),
                      sort_keys=True, separators=(",", ":"))
    return sha256(body.encode()).hexdigest()


def analyze_normal_surface(triangulation, coordinates, *, record_trace=False,
                           check=None, max_cycles=None):
    """Compute aggregate topology and an optional independently replayable proof.

    ``max_cycles`` bounds each of at most five orbit calls. All cancellation
    exceptions propagate; no partial result is a topology certificate.
    A positive ``certifies_compressing_disk`` answer is relative to the stated
    ambient preconditions. False is inconclusive for boundary essentiality on
    general higher-genus boundaries; on a torus the mod-two test is complete
    for a single embedded boundary circle.
    """
    if type(record_trace) is not bool:
        raise ValueError("record_trace must be Boolean")
    result, queries, facts, graph = _queries(triangulation, coordinates, check)
    outputs = {}
    for name, (size, pairings) in queries.items():
        _poll(check)
        outputs[name] = analyze_orbits(size, pairings, record_trace=record_trace,
                                      check=check, max_cycles=max_cycles)
    parity = _parity_certificate(graph, check)
    summary = _summary({name: value["orbit_count"] for name, value in outputs.items()},
                       facts, parity["nonzero"])
    response = {"summary": summary, "extraction": result.statistics(),
                "orbit_stats": {name: value["stats"] for name, value in outputs.items()},
                "scope": "supplied normal surface in a compact triangulated 3-manifold; "
                         "ambient validity and knot-exterior provenance are preconditions"}
    if record_trace:
        response["certificate"] = {"version": 1,
            "input_sha256": _fingerprint(triangulation, coordinates),
            "queries": {name: value["certificate"] for name, value in outputs.items()},
            "boundary_homology": parity, "summary": summary}
    return response


def verify_normal_surface_certificate(triangulation, coordinates, certificate, *, check=None):
    """Replay topology evidence without invoking any interval-orbit search."""
    from .interval_orbit_verify import verify_orbit_certificate
    if (type(certificate) is not dict or set(certificate) != {
            "version", "input_sha256", "queries", "boundary_homology", "summary"} or
            type(certificate["version"]) is not int or certificate["version"] != 1):
        return False
    _, queries, facts, graph = _queries(triangulation, coordinates, check)
    if certificate["input_sha256"] != _fingerprint(triangulation, coordinates):
        return False
    proofs = certificate["queries"]
    if type(proofs) is not dict or set(proofs) != set(queries):
        return False
    counts = {}
    for name, (size, pairings) in queries.items():
        _poll(check)
        if not verify_orbit_certificate(size, pairings, proofs[name], check=check):
            return False
        counts[name] = encoded_integer(proofs[name]["orbit_count"])
    parity = certificate["boundary_homology"]
    if not _verify_parity(graph, parity, check):
        return False
    expected = _summary(counts, facts, parity["nonzero"])
    supplied = certificate["summary"]
    if type(supplied) is not dict or set(supplied) != set(expected):
        return False
    for key, value in expected.items():
        if type(value) is bool:
            if type(supplied[key]) is not bool or supplied[key] != value:
                return False
        else:
            try:
                if encoded_integer(supplied[key]) != value:
                    return False
            except ValueError:
                return False
    return True


def main():
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON with triangulation and coordinates")
    parser.add_argument("--certificate", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    if type(data) is not dict or set(data) != {"triangulation", "coordinates"}:
        raise ValueError("input requires exactly triangulation and coordinates")
    result = analyze_normal_surface(data["triangulation"], data["coordinates"],
                                    record_trace=args.certificate)
    text = json.dumps(encode_large_integers(result), indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
